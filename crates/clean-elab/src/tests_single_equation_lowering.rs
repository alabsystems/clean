// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A definition given by ONE equation over several positions lowers as Lean's
//! `expandMatchAltsIntoMatch` (`Lean/Elab/Binders.lean`) writes it — `@fun x₁
//! … xₙ => match x₁, …, xₙ with …`, the arity taken from the syntax — rather
//! than as one `Prod` tuple whose arity is re-derived from its spine.
//!
//! Every fixture elaborates as written on the pinned v4.30.0-rc2 `lean`
//! binary (2026-09-12).

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(&mut env, d) {
            panic!("{what}: {e:?}");
        }
    }
}

/// Every position a variable: the codomain depends on both positions, which
/// the tuple's motive could not express (the kernel refused `natDecEq2`).
#[test]
fn test_single_equation_variables_with_dependent_codomain() {
    accepts(
        "def natDecEq2 : (a b : Nat) → Decidable (a = b)\n\
         \x20 | a, b => Nat.decEq a b\n\
         def addEqn : Nat → Nat → Nat\n\
         \x20 | a, _ => a + 1\n\
         theorem addEqn_val : addEqn 2 5 = 3 := rfl\n",
        "`| a, b => …` over a dependent codomain must elaborate",
    );
}

/// A LAST position that is itself an anonymous constructor: the spine
/// re-derivation counted it as more positions (`Unique.subsingleton_unique'`,
/// Mathlib `Logic/Unique.lean`).
#[test]
fn test_single_equation_last_position_anonymous_constructor() {
    accepts(
        "structure P2 where\n\
         \x20 a : Nat\n\
         \x20 b : Nat\n\
         def eqnPair : P2 → P2 → Nat\n\
         \x20 | ⟨x, _⟩, ⟨y, _⟩ => x + y\n\
         theorem eqnPair_val : eqnPair ⟨1, 2⟩ ⟨3, 4⟩ = 4 := rfl\n\
         universe u\n\
         structure Unique' (α : Sort u) extends Inhabited α where\n\
         \x20 uniq : ∀ a : α, a = default\n\
         theorem ss_shape {α : Sort u} : ∀ h₁ h₂ : Unique' α, h₁ = h₂ → True\n\
         \x20 | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => fun _ => True.intro\n",
        "two anonymous-constructor positions are two positions",
    );
}

/// Positions bind the type's binders in order, implicit ones included (the
/// `@` of `@fun`), and `rfl` / dotted names are constructor patterns.
#[test]
fn test_single_equation_implicit_rfl_and_dotted_positions() {
    accepts(
        "def gImpl : {n : Nat} → Fin (n+1) → Nat\n\
         \x20 | _, x => x.val\n\
         def gImpl2 : {n : Nat} → Fin (n+1) → Nat → Nat\n\
         \x20 | _, x, k => x.val + k\n\
         theorem eq_sub {P : Nat → Prop} {a b : Nat} : a = b → P a → P b\n\
         \x20 | rfl, h => h\n\
         def pu : PUnit → Nat → Nat\n\
         \x20 | PUnit.unit, n => n\n\
         theorem pu_val : pu PUnit.unit 3 = 3 := rfl\n",
        "implicit, `rfl` and dotted-constructor positions must elaborate",
    );
}

/// An equation the tuple encoding already counts correctly keeps it, and
/// with it the recursion lowering that recognizes that shape — with the
/// VALUES Lean gives, not only acceptance.
///
/// `pr ⟨x, y⟩ n` recurses on `n` and swaps the pair. Written as one equation
/// whose body matches `n`, the `.rec` on `n` sat inside the destructuring of
/// the pair, so the induction hypothesis reused the OUTER `x`: this fixture
/// used to elaborate with `pr ⟨1, 2⟩ 1 = 1` provable by `rfl` (Lean 4.8.0:
/// `2`; measured 2026-09-25), and was refused loudly since
/// (`check_recursive_minors_closed`). Since 2026-09-26 the destructuring is
/// moved into the arms of the match on `n` (`structural::hoist_recursive_match`),
/// so the one-equation form computes Lean's value too; the false value stays
/// unprovable. Written as two equations, the decreasing column is lowered
/// outermost directly.
#[test]
fn test_single_equation_recursive_tuple_shape_still_elaborates() {
    let single = "structure P2 where\n\
         \x20 a : Nat\n\
         \x20 b : Nat\n\
         def pr : P2 → Nat → Nat\n\
         \x20 | ⟨x, y⟩, n => match n with\n\
         \x20   | 0 => x\n\
         \x20   | k+1 => pr ⟨y, x⟩ k\n\
         theorem pr_false : pr ⟨1, 2⟩ 1 = 1 := rfl\n\
         theorem pr_one : pr ⟨1, 2⟩ 1 = 2 := rfl\n";
    let mut env = Environment::with_prelude();
    let decls = parse_file(single).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let outcomes: Vec<_> = decls
        .iter()
        .map(|d| elaborate_decl_and_register_with_warning(&mut env, d))
        .collect();
    assert!(
        outcomes[1].is_ok()
            && env
                .get_const(&clean_kernel::Name::from_string("pr"))
                .is_some(),
        "the one-equation form must elaborate: {:?}",
        outcomes[1].as_ref().err()
    );
    assert!(
        outcomes[3].is_ok()
            && env
                .get_const(&clean_kernel::Name::from_string("pr_one"))
                .is_some(),
        "Lean's `pr ⟨1, 2⟩ 1 = 2` must register: {:?}",
        outcomes[3].as_ref().err()
    );
    assert!(
        outcomes[2].is_err()
            && env
                .get_const(&clean_kernel::Name::from_string("pr_false"))
                .is_none(),
        "the false `pr ⟨1, 2⟩ 1 = 1` must not register"
    );
    accepts(
        "structure P2 where\n\
         \x20 a : Nat\n\
         \x20 b : Nat\n\
         def pr : P2 → Nat → Nat\n\
         \x20 | ⟨x, _⟩, 0 => x\n\
         \x20 | ⟨x, y⟩, k+1 => pr ⟨y, x⟩ k\n\
         theorem pr_one : pr ⟨1, 2⟩ 1 = 2 := rfl\n\
         theorem pr_two : pr ⟨1, 2⟩ 2 = 1 := rfl\n",
        "the two-equation form lowers the decreasing column outermost",
    );
}

/// SEVERAL equations whose LAST position is itself a tuple or anonymous
/// constructor: that position's own `Prod.mk` used to be counted as more
/// positions ("expected constructor of Nat, got constructor Prod.mk of Prod",
/// measured 2026-09-20 on main at `5e2e6dc0e`). Lean's arity is the number of
/// comma-separated patterns (`getMatchAltsNumPatterns`). Every fixture
/// elaborates on the pinned v4.30.0-rc2 `lean` binary (2026-09-20), and the
/// `rfl` theorems pin the VALUES, not only acceptance.
///
/// The `fun | …` lambda shares the encoding. OPEN, measured the same day and
/// unchanged by this: the multi-arm lambda `fun | 0, q => q.1 | n + 1, q => n
/// + q.2` still fails "Unknown identifier: q" (main fails it identically, and
/// it has no tuple in any position).
#[test]
fn test_multi_equation_last_position_tuple_is_one_position() {
    accepts(
        "structure P2 where\n\
         \x20 a : Nat\n\
         \x20 b : Nat\n\
         def eqnMulti : Nat → P2 → Nat\n\
         \x20 | 0, ⟨x, _⟩ => x\n\
         \x20 | n + 1, ⟨_, y⟩ => n + y\n\
         theorem eqnMulti_val : eqnMulti 2 ⟨3, 4⟩ = 5 := rfl\n\
         theorem eqnMulti_val0 : eqnMulti 0 ⟨3, 4⟩ = 3 := rfl\n\
         def eqnMultiTuple : Nat → Nat × Nat → Nat\n\
         \x20 | 0, (x, _) => x\n\
         \x20 | n + 1, (_, y) => n + y\n\
         theorem eqnMultiTuple_val : eqnMultiTuple 2 (3, 4) = 5 := rfl\n\
         def eqnThree : Nat → Nat → P2 → Nat\n\
         \x20 | 0, _, ⟨x, _⟩ => x\n\
         \x20 | n + 1, m, ⟨_, y⟩ => n + m + y\n\
         theorem eqnThree_val : eqnThree 2 1 ⟨3, 4⟩ = 6 := rfl\n\
         def funBool : Bool → Nat × Nat → Nat := fun\n\
         \x20 | true, (x, _) => x\n\
         \x20 | false, (_, y) => y\n\
         theorem funBool_true : funBool true (3, 4) = 3 := rfl\n\
         theorem funBool_false : funBool false (3, 4) = 4 := rfl\n",
        "a tuple in the last position is ONE position",
    );
}

/// Controls for the change above: the shapes that already worked keep their
/// lowering and their values — a tuple in a NON-last position, a single
/// position that is a tuple, and structural recursion over plain positions.
#[test]
fn test_multi_equation_other_positions_keep_their_lowering() {
    accepts(
        "structure P2 where\n\
         \x20 a : Nat\n\
         \x20 b : Nat\n\
         def ctlFirst : P2 → Nat → Nat\n\
         \x20 | ⟨x, _⟩, 0 => x\n\
         \x20 | ⟨_, y⟩, n + 1 => n + y\n\
         theorem ctlFirst_val : ctlFirst ⟨3, 4⟩ 2 = 5 := rfl\n\
         def ctlOnePos : Nat × Nat → Nat\n\
         \x20 | (0, b) => b\n\
         \x20 | (a + 1, _) => a\n\
         theorem ctlOnePos_val : ctlOnePos (3, 4) = 2 := rfl\n\
         def ctlAdd : Nat → Nat → Nat\n\
         \x20 | 0, m => m\n\
         \x20 | n + 1, m => ctlAdd n m + 1\n\
         theorem ctlAdd_val : ctlAdd 2 3 = 5 := rfl\n",
        "positions that were counted correctly are unchanged",
    );
}
