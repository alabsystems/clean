// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Where an application's argument run ends: a `·` bullet is a tactic block
//! with its own column (Lean's `cdotTk tacticSeqIndentGt`), a bracketed group
//! clears the saved position (`withoutPosition`), and a `postfix:max`
//! operator on an application HEAD binds before the arguments.
//!
//! Every accepted fixture elaborates as written on the pinned v4.30.0-rc2
//! `lean` binary (2026-09-12); the one refused fixture is refused there too
//! ("No goals to be solved").

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, src) {
        panic!("{what}: {e}");
    }
}

/// `Injective.extend_comp` (Mathlib `Logic/Function/Basic.lean:742-749`):
/// the term of `obtain … := h₃` inside a bullet used to run on across the
/// next tactic lines.
#[test]
fn test_bullet_obtain_term_stops_at_bullet_column() {
    accepts(
        "theorem ext_comp_shape (p q : Prop) [Decidable p] [Decidable q] (hq : q) \
         (h₃ : p ∧ q) : q := by\n\
         \x20 by_cases hp : p\n\
         \x20 · obtain ⟨a, b⟩ := h₃\n\
         \x20   by_cases h₂ : q\n\
         \x20   · exact h₂\n\
         \x20   · exact hq\n\
         \x20 · exact hq\n",
        "a bullet's `obtain` term must stop at the bullet's own column",
    );
}

/// `Prod.lt_iff` (Mathlib `Order/Basic.lean:922`): `· by_cases … ≤ …`
/// followed by a nested bullet list.
#[test]
fn test_bullet_by_cases_with_nested_bullets() {
    accepts(
        "theorem ltiff_shape (a b : Nat) (p : Prop) (hp : p) : p ∧ p := by\n\
         \x20 refine ⟨?_, ?_⟩\n\
         \x20 · by_cases h₁ : b ≤ a\n\
         \x20   · exact hp\n\
         \x20   · exact hp\n\
         \x20 · exact hp\n",
        "nested bullets belong to their parent bullet",
    );
}

#[test]
fn test_bullet_have_apply_refine_then_next_line() {
    accepts(
        "theorem plain_bullet (q : Prop) (hq : q) : q ∧ q := by\n\
         \x20 constructor\n\
         \x20 · have hh : True := True.intro\n\
         \x20   exact hq\n\
         \x20 · exact hq\n\
         theorem b_apply (q : Prop) (hq : q) : (q ∧ q) ∧ q := by\n\
         \x20 constructor\n\
         \x20 · apply And.intro\n\
         \x20   exact hq\n\
         \x20   exact hq\n\
         \x20 · exact hq\n\
         theorem b_refine (q : Prop) (hq : q) : (q ∧ q) ∧ q := by\n\
         \x20 constructor\n\
         \x20 · refine ⟨?_, ?_⟩\n\
         \x20   exact hq\n\
         \x20   exact hq\n\
         \x20 · exact hq\n",
        "a term tactic inside a bullet must not swallow the next tactic line",
    );
}

#[test]
fn test_bullet_first_tactic_on_next_line() {
    accepts(
        "theorem b_nextline (q : Prop) (hq : q) : q ∧ q := by\n\
         \x20 constructor\n\
         \x20 ·\n\
         \x20   have hh : True := True.intro\n\
         \x20   exact hq\n\
         \x20 · exact hq\n",
        "a bullet's column is its first tactic's column",
    );
}

#[test]
fn test_bullet_seq_focus_stays_inside_the_bullet() {
    accepts(
        "theorem b_seqfocus (p q : Prop) [Decidable p] (hq : q) : q ∧ q := by\n\
         \x20 constructor\n\
         \x20 · by_cases hp : p <;> exact hq\n\
         \x20 · exact hq\n",
        "`· t1 <;> t2` is `· (t1 <;> t2)`",
    );
}

#[test]
fn test_bullet_nested_under_constructor() {
    accepts(
        "theorem nested_ctor (q : Prop) (hq : q) : (q ∧ q) ∧ q := by\n\
         \x20 constructor\n\
         \x20 · constructor\n\
         \x20   · exact hq\n\
         \x20   · exact hq\n\
         \x20 · exact hq\n",
        "a same-column bullet under a bullet is nested in it",
    );
}

/// `constructor; · exact hq; · exact hq`: the `;` belongs to the FIRST
/// bullet's own sequence, so the second bullet is nested in the first and
/// finds no goal. Lean refuses it ("No goals to be solved"); Clean used to
/// read the two bullets as siblings and accept it.
#[test]
fn test_bullet_semicolon_joined_bullets_nest_as_in_lean() {
    let mut env = Environment::with_prelude();
    let src = "theorem semi_bullets (q : Prop) (hq : q) : q ∧ q := by\n\
               \x20 constructor; · exact hq; · exact hq\n";
    assert!(
        elab(&mut env, src).is_some(),
        "the second `;`-joined bullet is nested in the first and has no goal"
    );
}

/// Lean's `withoutPosition`: a bracketed continuation line is never cut at
/// an enclosing block's column, at the `by` column or at a bullet's.
#[test]
fn test_bracketed_continuation_ignores_block_columns() {
    accepts(
        "theorem br_paren (h : 2 = 2) : 2 = 2 := by\n\
         \x20 exact (id\n\
         \x20 h)\n\
         theorem br_anon (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n\
         \x20 exact ⟨id\n\
         \x20 hp, hq⟩\n\
         theorem br_bullet (h : 2 = 2) : 2 = 2 ∧ True := by\n\
         \x20 constructor\n\
         \x20 · exact (id\n\
         \x20   h)\n\
         \x20 · trivial\n\
         theorem br_bullet_left (h : 2 = 2) : 2 = 2 ∧ True := by\n\
         \x20 constructor\n\
         \x20 · exact (id\n\
         \x20 h)\n\
         \x20 · trivial\n\
         theorem br_ctl (h : 2 = 2) : 2 = 2 := by\n\
         \x20 exact (id\n\
         \x20   h)\n",
        "a bracketed group has no saved position",
    );
}

/// `Pi.compl_apply` (Mathlib `Order/Basic.lean:513`): `xᶜ i` is `(xᶜ) i`.
///
/// Not covered here: `f (xᶜ i)` against a CONCRETE argument type. It parses
/// the same way, but `elab_app` still elaborates a non-identifier head with
/// the whole application's expected type (Lean's `elabAppFn` uses `none`),
/// which is a separate elaborator defect.
#[test]
fn test_max_postfix_on_application_head() {
    let mut env = Environment::with_prelude();
    let prefix = "class MyCompl (α : Type) where\n\
                  \x20 compl : α → α\n\
                  postfix:max \"ᶜ\" => MyCompl.compl\n\
                  instance instPiCompl : MyCompl (Nat → Bool) := ⟨fun f n => !(f n)⟩\n";
    if let Some(e) = elab(&mut env, prefix) {
        panic!("the notation prelude must elaborate: {e}");
    }
    for (name, src) in [
        (
            "compl_apply",
            "theorem compl_apply (x : Nat → Bool) (i : Nat) : xᶜ i = !(x i) := rfl\n",
        ),
        (
            "compl_apply_ctl",
            "theorem compl_apply_ctl (x : Nat → Bool) (i : Nat) : (xᶜ) i = !(x i) := rfl\n",
        ),
    ] {
        let full = format!("{prefix}{src}");
        let mut env = Environment::with_prelude();
        if let Some(e) = elab(&mut env, &full) {
            panic!("`{name}`: a max postfix on the head binds before the arguments: {e}");
        }
    }
}
