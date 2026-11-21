// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The TERM, pattern and `do` forms of the battery: `exists x, p`,
//! `.partial`, `open … in` as an equation body, a named pattern in argument
//! position, literal `let` bodies, `else ⏎ if` in `do`, `module` as an
//! identifier, and the `.rfl` pattern.

use crate::common::*;

// --- `exists x, p` -------------------------------------------------------

#[test]
fn test_exists_keyword_is_exists() {
    let src = "theorem exists_kw : exists n : Nat, n + 1 = 2 := ⟨1, rfl⟩\n\n\
               theorem exists_kw_or (n : Nat) : (exists r, r = n) ∨ (exists (e : Nat), e + 1 = n) := \
               Or.inl ⟨n, rfl⟩\n";
    expect_axiom_free(src, "`exists x, p`", &["exists_kw", "exists_kw_or"]);
}

#[test]
fn test_exists_keyword_false_witness_is_rejected() {
    expect_refused_at(
        "theorem exists_kw_twin : exists n : Nat, n + 1 = 0 := ⟨0, rfl⟩\n",
        "a false `exists` witness",
        "exists_kw_twin",
        MISMATCH,
    );
}

// --- `.partial` ----------------------------------------------------------

const PARTIAL_CTOR: &str = "inductive V where\n  | «partial» : Nat → V\n  | other : V\n\n\
                            def V.isPartial : V → Bool\n  | .partial _ => true\n  | _ => false\n\n";

#[test]
fn test_keyword_spelled_constructor_pattern_matches_that_constructor() {
    let src = format!(
        "{PARTIAL_CTOR}theorem V.isPartial_partial (n : Nat) : (V.partial n).isPartial = true := rfl\n\n\
         theorem V.isPartial_other : V.other.isPartial = false := rfl\n"
    );
    expect_axiom_free(
        &src,
        "a `.partial` pattern",
        &["V.isPartial_partial", "V.isPartial_other"],
    );
}

#[test]
fn test_keyword_spelled_constructor_pattern_is_not_a_catch_all() {
    // Were `.partial _` a binder pattern, every value would be partial.
    let src = format!("{PARTIAL_CTOR}theorem V.isPartial_twin : V.other.isPartial = true := rfl\n");
    expect_refused_at(
        &src,
        "`.partial _` read as a catch-all",
        "V.isPartial_twin",
        MISMATCH,
    );
}

// --- `open … in` as an equation body -------------------------------------

const PICK: &str = "noncomputable def pick : Nat → Nat\n  | n =>\n    open Classical in\n    \
                    if n = 0 then 1 else n\n\n";

#[test]
fn test_open_in_term_equation_body_elaborates() {
    // Lean 4.8 picks `instDecidableEqNat` over the low-priority scoped
    // `Classical.propDecidable`, so `pick 0` computes and depends on no
    // axiom ('pick_zero' does not depend on any axioms) — foundational ones
    // included: choosing `Classical.propDecidable` would reach
    // `Classical.choice`, which `assert_axiom_free` alone does not see.
    let src = format!("{PICK}theorem pick_zero : pick 0 = 1 := rfl\n");
    let env = expect_accepted(&src, "`open Classical in` as an equation body");
    assert_no_axioms(&env, "pick_zero");
    assert_no_axioms(&env, "pick");
}

#[test]
fn test_open_in_term_equation_body_value_is_checked() {
    let src = format!("{PICK}theorem pick_twin : pick 0 = 0 := rfl\n");
    expect_refused_at(&src, "a wrong value for `pick 0`", "pick_twin", MISMATCH);
}

// --- named pattern in argument position ----------------------------------

const NAMED_PAT: &str = "inductive C where\n  | agg : Nat → C\n  | arr : Nat → C\n  | lit : Nat → C\n\n\
                         inductive I where\n  | const : Nat → C → I\n  | nop : I\n\n\
                         def size : I → Nat\n  | .const _ c@(.agg n) => n + (match c with | .agg m => m | _ => 0)\n  \
                         | .const _ (.arr n) => n\n  | _ => 0\n\n";

#[test]
fn test_named_pattern_argument_binds_the_matched_value() {
    let src = format!(
        "{NAMED_PAT}theorem size_agg : size (.const 0 (.agg 3)) = 6 := rfl\n\n\
         theorem size_lit : size (.const 0 (.lit 3)) = 0 := rfl\n"
    );
    expect_axiom_free(
        &src,
        "`c@(.agg n)` in a constructor argument",
        &["size_agg", "size_lit"],
    );
}

#[test]
fn test_named_pattern_argument_does_not_match_other_constructors() {
    let src = format!("{NAMED_PAT}theorem size_twin : size (.const 0 (.lit 3)) = 3 := rfl\n");
    expect_refused_at(
        &src,
        "`c@(.agg n)` matching a `.lit`",
        "size_twin",
        MISMATCH,
    );
}

// --- literal let bodies --------------------------------------------------

#[test]
fn test_let_body_string_literal_computes() {
    let def = "def sval (n : Nat) : String :=\n  let d := toString n\n  \"v:\" ++ d\n\n";
    let src = format!("{def}theorem sval_ok : sval 3 = \"v:3\" := rfl\n");
    expect_axiom_free(&src, "a string-literal let body", &["sval_ok"]);
    let src = format!("{def}theorem sval_twin : sval 3 = \"v:4\" := rfl\n");
    expect_refused_at(
        &src,
        "a wrong string-literal let body value",
        "sval_twin",
        MISMATCH,
    );
}

#[test]
fn test_let_body_array_literal_computes() {
    // `#[` on the line after a `let` value is the body (Lean: `arr 3 =
    // #[3, 3]` by `rfl`, and `#[3, 4]` refused with "type mismatch").
    let def = "def arr (n : Nat) : Array Nat :=\n  let d := n\n  #[d, d]\n\n";
    let src = format!("{def}theorem arr_ok : arr 3 = #[3, 3] := rfl\n");
    expect_axiom_free(&src, "an array-literal let body", &["arr_ok"]);
    let src = format!("{def}theorem arr_twin : arr 3 = #[3, 4] := rfl\n");
    expect_refused_at(
        &src,
        "a wrong array-literal let body value",
        "arr_twin",
        MISMATCH,
    );
}

// --- `else ⏎ if` in `do` -------------------------------------------------

const DO_ELSE_BLOCK: &str = "def h4 (n : Nat) (e : Except String Nat) : Except String Nat := do\n  \
                             if n == 0 then\n    pure 0\n  else\n    if n == 1 then\n      throw \"one\"\n    \
                             let k ← e\n    if k != 0 then\n      throw \"nz\"\n    pure (k + 1)\n\n";

#[test]
fn test_do_else_block_starting_with_if_runs_every_statement() {
    let src = format!(
        "{DO_ELSE_BLOCK}theorem h4_ok : h4 2 (.ok 0) = .ok 1 := rfl\n\n\
         theorem h4_one : h4 1 (.ok 0) = .error \"one\" := rfl\n"
    );
    expect_axiom_free(
        &src,
        "an `else` block whose first statement is an `if`",
        &["h4_ok", "h4_one"],
    );
}

#[test]
fn test_do_else_block_value_is_not_the_inner_if_alone() {
    let src = format!("{DO_ELSE_BLOCK}theorem h4_twin : h4 2 (.ok 0) = .ok 0 := rfl\n");
    expect_refused_at(
        &src,
        "a wrong value for the `else` block",
        "h4_twin",
        MISMATCH,
    );
}

/// The inner `if` sits at the OUTER `if`'s column: still a block, and the
/// block takes the statements after it (pinned Lean: `(ecol false false,
/// ecol true false, ecol false true) = (4, 1, 2)`). Every branch here
/// RETURNS, so these values are the same under the `else if` chain reading;
/// `DO_ELSE_FALL_THROUGH` and `ecol_mut` are the rows that tell the two
/// apart.
const DO_ELSE_SAME_COLUMN: &str = "def ecol (a b : Bool) : Nat := Id.run do\n  if a then\n    \
                                   return 1\n  else\n  if b then\n    return 2\n  return 4\n\n";

#[test]
fn test_do_else_block_at_the_if_column_computes() {
    let src = format!(
        "{DO_ELSE_SAME_COLUMN}theorem ecol_ff : ecol false false = 4 := rfl\n\n\
         theorem ecol_tf : ecol true false = 1 := rfl\n\n\
         theorem ecol_ft : ecol false true = 2 := rfl\n"
    );
    expect_axiom_free(
        &src,
        "an `else` block at the `if`'s own column",
        &["ecol_ff", "ecol_tf", "ecol_ft"],
    );
    let src = format!("{DO_ELSE_SAME_COLUMN}theorem ecol_twin : ecol true false = 4 := rfl\n");
    expect_refused_at(
        &src,
        "a wrong value for `ecol true false`",
        "ecol_twin",
        MISMATCH,
    );
}

/// The `then` branch FALLS THROUGH (`pure x`, no `return`), so the two
/// readings of `else ⏎ if` part ways: as a block, the `else` block takes `x :=
/// x + 10` and `return x`, the outer `if` ends the `do` block and `ecol4 true
/// false` is `5`; read as an `else if` chain, those statements would follow
/// the outer `if` and make it `15` (or refuse the non-`Unit` `then` branch).
/// Pinned Lean 4.8.0: `5`, `10`, `12`, and `= 15` refused ("type mismatch").
const DO_ELSE_FALL_THROUGH: &str =
    "def ecol4 (a b : Bool) : Nat := Id.run do\n  let mut x := 0\n  \
                                    if a then\n    x := 5\n    pure x\n  else\n  if b then\n    \
                                    x := 2\n  x := x + 10\n  return x\n\n";

#[test]
fn test_do_else_block_at_the_if_column_is_a_block_not_an_else_if_chain() {
    let src = format!(
        "{DO_ELSE_FALL_THROUGH}theorem e_tf : ecol4 true false = 5 := rfl\n\n\
         theorem e_ff : ecol4 false false = 10 := rfl\n\n\
         theorem e_ft : ecol4 false true = 12 := rfl\n"
    );
    expect_axiom_free(
        &src,
        "an `else` block at the `if`'s column after a falling-through `then`",
        &["e_tf", "e_ff", "e_ft"],
    );
    let src = format!("{DO_ELSE_FALL_THROUGH}theorem e_twin : ecol4 true false = 15 := rfl\n");
    expect_refused_at(
        &src,
        "the `else if` chain reading of `ecol4 true false`",
        "e_twin",
        MISMATCH,
    );
}

#[test]
fn test_do_else_block_at_the_if_column_owns_the_later_statements() {
    // Lean 4.8 refuses `ecol_mut`: the `else` block takes `x := x + 10` and
    // `return x`, so the outer block ends with the `if`, whose `then`
    // branch `x := 1` is not a `Nat` ("application type mismatch … pure
    // PUnit.unit"). Reading the two statements as the outer block's would
    // accept it.
    let src = "def ecol_mut (a b : Bool) : Nat := Id.run do\n  let mut x := 0\n  if a then\n    \
               x := 1\n  else\n  if b then\n    x := 2\n  x := x + 10\n  return x\n";
    expect_refused_at(
        src,
        "the statements after an `else` block's `if`",
        "ecol_mut",
        &[],
    );
}

// --- `module` as an identifier -------------------------------------------

const MODULE_IDENT: &str = "structure Batch where\n  module : Nat\n  runs : List Nat\n\n\
                            def module (j : Nat) : Nat := j + 1\n\n\
                            def batch (j : Nat) : Batch := { module := module j, runs := [] }\n\n";

#[test]
fn test_module_identifier_is_a_field_a_def_and_a_term() {
    let src = format!("{MODULE_IDENT}theorem batch_ok : (batch 1).module = 2 := rfl\n");
    expect_axiom_free(&src, "`module` as a field, a def and a term", &["batch_ok"]);
}

#[test]
fn test_module_identifier_value_is_checked() {
    let src = format!("{MODULE_IDENT}theorem batch_twin : (batch 1).module = 1 := rfl\n");
    expect_refused_at(
        &src,
        "a wrong value through the `module` field",
        "batch_twin",
        MISMATCH,
    );
}

#[test]
fn test_module_is_not_a_tactic() {
    // Lean 4.8.0: "unknown tactic". The reason is matched after the
    // `module_tac: ` label, which itself spells "module".
    expect_refused_at(
        "theorem module_tac (a b : Nat) : a + b = b + a := by\n  module\n",
        "`by module`",
        "module_tac",
        &["unknown tactic 'module'"],
    );
}

// --- `.rfl` is a dotted identifier ---------------------------------------

// The constructor is declared escaped: a bare `rfl` there is one of Clean's
// pinned keyword divergences (`tests_name_strategy::CLEAN_ONLY_RESERVED`);
// Lean 4.8.0 accepts both spellings. The PATTERN `.rfl` is the subject.
const DOT_RFL: &str = "inductive T where\n  | «rfl»\n  | other\n\n\
                       def T.isRfl : T → Bool\n  | .rfl => true\n  | .other => false\n\n";

#[test]
fn test_dot_rfl_pattern_selects_the_expected_types_constructor() {
    let src = format!(
        "{DOT_RFL}theorem t_rfl : T.rfl.isRfl = true := rfl\n\n\
         theorem t_other : T.other.isRfl = false := rfl\n"
    );
    expect_axiom_free(&src, "`.rfl` naming `T.rfl`", &["t_rfl", "t_other"]);
}

#[test]
fn test_dot_rfl_pattern_is_not_a_catch_all() {
    let src = format!("{DOT_RFL}theorem t_twin : T.other.isRfl = true := rfl\n");
    expect_refused_at(&src, "`.rfl` read as a catch-all", "t_twin", MISMATCH);
}

#[test]
fn test_dot_rfl_pattern_on_an_equation_is_refused() {
    // Lean 4.8.0: "invalid dotted identifier notation, unknown identifier
    // `Eq.rfl` from expected type" — `.rfl` is never the keyword `rfl`.
    expect_refused_at(
        "def f1 (h : 1 = 1) : Nat := match h with | .rfl => 0\n",
        "`.rfl` against an `Eq`",
        "f1",
        &[],
    );
}

const NAMED_DOT_HEADER: &str = r#"
inductive DotBox where
  | red : DotBox
  | blue : DotBox

def DotBox.pick (a b : DotBox) : DotBox := a
def DotBox.tag {Label : Type} (x : Label) (self : DotBox) : Label := x
def DotBox.payload {Metadata : Type} : DotBox → Option Metadata := fun _ => none
"#;

#[test]
fn named_dot_arguments_use_the_full_telescope_and_keep_the_receiver_position() {
    let source = format!(
        "{NAMED_DOT_HEADER}{}",
        r#"
theorem before (box : DotBox) : box.tag (Label := Nat) 7 = 7 := rfl
theorem after (box : DotBox) : box.tag (x := 7) (Label := Nat) = 7 := rfl
theorem anonymousSlot (box : DotBox) : box.payload (Metadata := Nat) = (none : Option Nat) := rfl
theorem secondReceiver (a b : DotBox) : b.pick (a := a) = a := rfl
theorem firstReceiver (a b : DotBox) : a.pick (b := b) = a := rfl
theorem ns (box : DotBox) : DotBox.tag (Label := Nat) 6 box = 6 := rfl
"#
    );
    let env = expect_accepted(&source, "named parameters around a projected receiver");
    for name in [
        "before",
        "after",
        "anonymousSlot",
        "secondReceiver",
        "firstReceiver",
        "ns",
    ] {
        assert_no_axioms(&env, name);
    }
}

#[test]
fn named_dot_arguments_refuse_unknown_duplicate_occupied_and_false_calls() {
    for (term, reason) in [
        (
            "box.tag (Label := Nat) (Label := Nat) 7 = 7",
            "already bound",
        ),
        ("box.tag (invented := Nat) 7 = 7", "unknown named argument"),
        ("box.pick (a := box) (b := box) = box", "no usable receiver"),
        ("box.tag (Label := Nat) 7 = 8", "mismatch"),
    ] {
        let source = format!("{NAMED_DOT_HEADER}theorem rejected (box : DotBox) : {term} := rfl\n");
        expect_refused_at(
            &source,
            "invalid named-dot call or equality",
            "rejected",
            &[reason],
        );
    }
}

#[test]
fn named_dot_arguments_expand_ellipsis_after_positioning_the_receiver() {
    let source = format!(
        "{NAMED_DOT_HEADER}{}",
        r#"
inductive DotItem : Nat → Type where
  | item (n : Nat) : DotItem n

def DotBox.item {Label : Type} (self : DotBox) (n : Nat) : DotItem n := DotItem.item n
def fromExpected (box : DotBox) : DotItem 4 := box.item (Label := Nat) ..
theorem expectedIndex (box : DotBox) : fromExpected box = DotItem.item 4 := rfl
abbrev DotTail := (n : Nat) → DotItem n
def DotBox.give {Flag : Type} (self : DotBox) : DotTail := DotItem.item
def tailExpected (box : DotBox) : DotItem 3 := box.give (Flag := Nat) ..
theorem reducedTail (box : DotBox) : tailExpected box = DotItem.item 3 := rfl
theorem noneLeft (box : DotBox) : box.payload (Metadata := Nat) .. = (none : Option Nat) := rfl
theorem withValue (box : DotBox) : box.tag (Label := Nat) 7 .. = 7 := rfl
"#
    );
    let env = expect_accepted(&source, "ellipsis fills the remaining explicit index");
    for name in ["expectedIndex", "reducedTail", "noneLeft", "withValue"] {
        assert_no_axioms(&env, name);
    }
    expect_refused_at(
        &format!(
            "{NAMED_DOT_HEADER}def missing (box : DotBox) : Nat := box.tag (Label := Nat) ..\n"
        ),
        "an unconstrained ellipsis hole must remain unsolved",
        "missing",
        &[],
    );
}

#[test]
fn named_dot_arguments_distinguish_reducible_aliases_from_ordinary_wrappers() {
    for (dec, rhs, wrong) in [("def", "r", "s"), ("abbrev", "s", "r")] {
        let header = format!(
            r#"
inductive Box | red | blue
{dec} WrapBox := Box
{dec} WrapFun := Nat → Nat

def Box.pick {{Tag : Type}} (first : WrapBox) (real : Box) : Box := real
def Box.pickPlain (first : WrapBox) (real : Box) : Box := real
def Function.pick {{Tag : Type}} (first : WrapFun) (real : Nat → Nat) : Nat := real 2
"#
        );
        for (ty, call, suffix) in [
            ("Box", "r.pick (Tag := Nat) s", ""),
            ("Box", "r.pickPlain s", ""),
            ("Nat → Nat", "r.pick (Tag := Nat) s", " 2"),
        ] {
            let decl = |target| {
                format!(
                    "{header}theorem positioned (r s : {ty}) : {call} = {target}{suffix} := rfl\n"
                )
            };
            let env = expect_accepted(
                &decl(rhs),
                "Lean receiver position under instances transparency",
            );
            assert_no_axioms(&env, "positioned");
            expect_refused_at(
                &decl(wrong),
                "a swapped receiver changes this method result",
                "positioned",
                &[],
            );
        }
    }
}
