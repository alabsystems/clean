// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the rcases pattern forms `-` (clear), `@pat`
//! (explicit), a parenthesized alternative inside an alternation, and
//! `rintro`'s binder group `(x y : t)` and trailing `: t`.
//!
//! Each module is parsed, elaborated against the builtin prelude and
//! kernel-checked. Every expectation was ground-truthed against the pinned
//! Lean toolchains (v4.8.0 and v4.30.0-rc2): a theorem asserted to fail here
//! fails there with the error quoted beside it.
//!
//! The motivating source is `TrustIr/Basic.lean:429` in trust-ir's Lean
//! semantics package, whose `rintro ⟨hlo, -⟩` died in the parser ("expected
//! identifier in rcases pattern, got Minus") and took every file importing
//! `TrustIr/Basic.lean` with it.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

const PREAMBLE: &str = "\
axiom P : Prop
axiom Q : Prop
axiom R : Prop
axiom A : Type
axiom pr : A → Prop
inductive Wrap : Prop where
  | mk {a : Nat} (h : a = a) : Wrap
";

/// Elaborate `PREAMBLE` then `source` against the builtin prelude; `Err`
/// names every declaration that failed to parse, elaborate or kernel-check.
fn elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let text = format!("{PREAMBLE}{source}");
    let decls = parse_file(&text).map_err(|e| format!("parse error: {e:?}"))?;
    let mut failures = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register(&mut env, &processed) {
            Ok(result) => collect_failures(&result, &mut failures),
            Err(e) => failures.push(format!("elaborate/kernel-check error: {e}")),
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n"))
    }
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn accepts(source: &str) {
    if let Err(e) = elaborate(source) {
        panic!("expected Clean to accept (Lean does):\n{source}\n--- got:\n{e}");
    }
}

fn rejects(source: &str) {
    assert!(
        elaborate(source).is_err(),
        "expected Clean to reject (Lean does):\n{source}"
    );
}

const VALID_CHAR: &str = "def validChar (v : Nat) : Prop :=
  v < 0x110000 ∧ ¬(0xD800 ≤ v ∧ v ≤ 0xDFFF)
";

#[test]
fn test_trust_ir_basic_valid_char_of_lt_256_kernel_checks() {
    // `TrustIr/Basic.lean:425-430`, its two `omega` calls replaced by the
    // arithmetic they decide: omega on these literals is another lane's cost
    // bug. `@` because Clean's prelude binds `Nat.lt_trans`'s and
    // `Nat.lt_of_le_of_lt`'s numbers explicitly where Lean's are implicit;
    // the `@` spelling means the same in both.
    accepts(&format!(
        "{VALID_CHAR}
theorem validChar_of_lt_256 {{v : Nat}} (h : v < 256) : validChar v := by
  refine ⟨@Nat.lt_trans v 256 0x110000 h (by decide), ?_⟩
  rintro ⟨hlo, -⟩
  exact absurd (@Nat.lt_of_le_of_lt 0xD800 v 256 hlo h) (by decide)
"
    ));
    // NEGATIVE CONTROL: clear the lower bound instead, and `assumption`
    // cannot find it. Lean: "tactic 'assumption' failed" ...
    rejects(&format!(
        "{VALID_CHAR}
theorem validChar_of_lt_256 {{v : Nat}} (h : v < 256) : validChar v := by
  refine ⟨@Nat.lt_trans v 256 0x110000 h (by decide), ?_⟩
  rintro ⟨-, hhi⟩
  exact absurd (@Nat.lt_of_le_of_lt 0xD800 v 256 (by assumption) h) (by decide)
"
    ));
    // ... while `_` keeps it, and the identical proof closes.
    accepts(&format!(
        "{VALID_CHAR}
theorem validChar_of_lt_256 {{v : Nat}} (h : v < 256) : validChar v := by
  refine ⟨@Nat.lt_trans v 256 0x110000 h (by decide), ?_⟩
  rintro ⟨_, hhi⟩
  exact absurd (@Nat.lt_of_le_of_lt 0xD800 v 256 (by assumption) h) (by decide)
"
    ));
}

#[test]
fn test_rintro_clear_field_leaves_the_other_field_usable() {
    accepts("theorem t : P ∧ Q → P := by\n  rintro ⟨hp, -⟩\n  exact hp\n");
    accepts("theorem t : P ∧ Q → Q := by\n  rintro ⟨-, hq⟩\n  exact hq\n");
}

#[test]
fn test_rintro_cleared_field_is_not_usable() {
    // NEGATIVE CONTROL. Lean: "tactic 'assumption' failed ... hp : P ⊢ Q".
    rejects("theorem t : P ∧ Q → Q := by\n  rintro ⟨hp, -⟩\n  assumption\n");
    // ...while `_` keeps the component (inaccessible), so the same proof
    // closes: what fails above is the clearing, not the naming.
    accepts("theorem t : P ∧ Q → Q := by\n  rintro ⟨hp, _⟩\n  assumption\n");
}

#[test]
fn test_obtain_and_rcases_clear_fields() {
    accepts("theorem t (h : P ∧ Q) : P := by\n  obtain ⟨hp, -⟩ := h\n  exact hp\n");
    accepts("theorem t (h : P ∧ Q) : Q := by\n  rcases h with ⟨-, hq⟩\n  exact hq\n");
    rejects("theorem t (h : P ∧ Q) : Q := by\n  obtain ⟨-, -⟩ := h\n  assumption\n");
}

#[test]
fn test_rcases_top_level_clear_removes_the_hypothesis() {
    // Lean: `rcases h with -` then "tactic 'assumption' failed ⊢ P".
    rejects("theorem t (h : P) : P := by\n  rcases h with -\n  assumption\n");
    accepts("theorem t (h : P) (hq : Q) : Q := by\n  rcases h with -\n  assumption\n");
}

#[test]
fn test_clearing_a_witness_clears_its_dependents() {
    // `tryClearMany'`: `hx : pr x` depends on the cleared `x`, so it goes too.
    // Lean: "unknown identifier 'hx'".
    rejects(
        "theorem t (h : ∃ x : A, pr x) : ∃ x : A, pr x := by
  obtain ⟨-, hx⟩ := h
  exact ⟨_, hx⟩
",
    );
    accepts(
        "theorem t (h : ∃ x : A, pr x) : ∃ x : A, pr x := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx⟩
",
    );
    // Clears run once, after every rintro pattern: `h : pr x` depends on
    // the cleared binder and is cleared with it. Lean: "unknown identifier 'h'".
    rejects(
        "theorem t : ∀ (x : A), pr x → True := by
  rintro - h
  exact (fun (_ : pr _) => True.intro) h
",
    );
    accepts("theorem t : ∀ (x : A), pr x → True := by\n  rintro - h\n  exact True.intro\n");
}

#[test]
fn test_clear_in_an_alternation() {
    accepts(
        "theorem t (h : P ∨ Q) (hr : R) : R := by
  rcases h with - | hq
  · exact hr
  · exact hr
",
    );
    rejects(
        "theorem t (h : P ∨ Q) : P ∨ Q := by
  rcases h with - | hq
  · exact Or.inl (by assumption)
  · exact Or.inr hq
",
    );
}

#[test]
fn test_tuple_skips_implicit_constructor_fields_without_at() {
    // `Wrap.mk {a : Nat} (h : a = a)`: `⟨h⟩` binds the EXPLICIT field.
    accepts(
        "theorem t (w : Wrap) : ∃ a : Nat, a = a := by
  obtain ⟨h⟩ := w
  exact ⟨_, h⟩
",
    );
}

#[test]
fn test_explicit_pattern_binds_implicit_constructor_fields() {
    accepts(
        "theorem t (w : Wrap) : ∃ a : Nat, a = a := by
  obtain @⟨a, h⟩ := w
  exact ⟨a, h⟩
",
    );
    // `@⟨h⟩`: `h` names the implicit `a : Nat`. Lean: "application type
    // mismatch ... h has type Nat".
    rejects(
        "theorem t (w : Wrap) : ∃ a : Nat, a = a := by
  obtain @⟨h⟩ := w
  exact ⟨_, h⟩
",
    );
}

#[test]
fn test_parenthesized_alternative_splits_again() {
    accepts(
        "theorem t (h : (P ∨ Q) ∨ R) : (P ∨ Q) ∨ R := by
  rcases h with (hp | hq) | hr
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr hq)
  · exact Or.inr hr
",
    );
}

#[test]
fn test_rintro_binder_group_and_trailing_type() {
    accepts("theorem t : ∀ (x y : Nat), x + y = x + y := by\n  rintro (x y : Nat)\n  rfl\n");
    accepts("theorem t : ∀ (x : Nat), x = x := by\n  rintro x : Nat\n  rfl\n");
    // The written type must match: `Bool` is not the binder type `Nat`.
    rejects("theorem t : ∀ (x y : Nat), x + y = x + y := by\n  rintro (x y : Bool)\n  rfl\n");
}

#[test]
fn test_obtain_without_value_asserts_the_type_first() {
    // `obtainNone`: the goal `⊢ P ∧ Q` comes first, then the destructured one.
    accepts(
        "theorem t (hp : P) (hq : Q) : Q ∧ P := by
  obtain ⟨h1, h2⟩ : P ∧ Q
  · exact ⟨hp, hq⟩
  exact ⟨h2, h1⟩
",
    );
    // Lean: "unknown identifier 'h2'" — the pattern's names are not in scope
    // in the first goal.
    rejects(
        "theorem t (hp : P) (hq : Q) : Q ∧ P := by
  obtain ⟨h1, h2⟩ : P ∧ Q
  · exact ⟨h2, h1⟩
  exact ⟨hp, hq⟩
",
    );
}

/// Named and several `rcases` targets (`casesTarget,*`, `casesTarget :=
/// (ident " : ")? term`), once pinned gaps here, closed with trust-ir G24
/// (ledger class (93)); each acceptance has a negative pinned Lean 4.8.0
/// refuses.
#[test]
fn test_rcases_named_and_several_targets() {
    // `h : o`: `o` is generalized with `h : o = x` and `x` is matched, so
    // each branch has `h : o = <ctor>`.
    accepts(
        "theorem t (o : Option Nat) (p : Prop) (hn : o = none → p)
    (hs : ∀ v, o = some v → p) : p := by
  rcases h : o with _ | v
  · exact hn h
  · exact hs v h
",
    );
    // Lean: `application type mismatch` — the `none` branch's `h` is
    // `o = none`.
    rejects(
        "theorem t (o : Option Nat) (p : Prop) (hn : o = none → p)
    (hs : ∀ v, o = some v → p) : p := by
  rcases h : o with _ | v
  · exact hs 0 h
  · exact hs v h
",
    );
    // Several targets: the tuple's components are spread over the targets
    // (`processConstructor`), so `a` is destructured and `b` cleared.
    accepts(
        "theorem t (a : P ∧ Q) (b : Q) : Q ∧ P := by
  rcases a, b with ⟨⟨x, y⟩, -⟩
  exact ⟨y, x⟩
",
    );
    // Lean: `application type mismatch` — `x : P` went to `a`'s first field.
    rejects(
        "theorem t (a : P ∧ Q) (b : Q) : Q ∧ P := by
  rcases a, b with ⟨⟨x, y⟩, -⟩
  exact ⟨x, y⟩
",
    );
}

#[test]
fn test_unsupported_obtain_targets_are_pinned_gaps() {
    // KNOWN GAP, pinned as a refusal: Lean (v4.8.0) ACCEPTS it. When Clean
    // learns the form, this row fails; turn it into `accepts` with a
    // negative. `obtain pat := term,+` spreads the tuple over the terms as
    // `rcases` does; Clean's `obtain` parses one term, so `, b` falls to
    // parser recovery.
    rejects(
        "theorem t (a : P ∧ Q) (b : Q) : Q ∧ P := by
  obtain ⟨⟨x, y⟩, -⟩ := a, b
  exact ⟨y, x⟩
",
    );
}
