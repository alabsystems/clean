// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Structure-instance PATTERNS: `fun | { a := x, .. } => x`.
//!
//! Lean has no separate pattern grammar — patterns ARE terms, so
//! `Lean.Parser.Term.structInst` parses in pattern position with no extra rule
//! and `Lean/Elab/PatternVar.lean:304-313` walks each field's value collecting
//! pattern variables (refusing a `with` source at :306-307 and preserving `..`
//! and the optional `: ty`). Clean's pattern parser is a hand-written closed
//! token set with no `{` arm, so `Mathlib/Order/Basic.lean`'s
//! `Preorder.toLE_injective` (L435) and `LinearOrder.toPartialOrder_injective`
//! (L451) died in parser recovery: "Unexpected token …: expected pattern, got
//! LBrace", one raw-declaration row and one `parser.recovery` row each.
//!
//! The fix is a `SurfacePattern::StructInst` node plus an `LBrace` arm, with the
//! field NAMES resolved to constructor POSITIONS in
//! `normalize_match_pattern_names_inner` — the one place the scrutinee type is
//! known, and the same place the `..` of a `.Ctor ..` pattern is materialized.
//!
//! ACCEPTANCE BAR: every positive case pins the produced VALUE with a `rfl`
//! theorem, so a pattern that binds the WRONG field cannot pass; the negatives
//! assert a LOUD failure rather than a silent wildcard.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// Two same-typed fields, so a pattern that binds the wrong slot produces a
/// DIFFERENT value and the `rfl` pin fails.
const FOO: &str = "
structure Foo where
  a : Nat
  b : Nat
";

/// A one-field parent and a child that extends it: the child literal's `le`
/// names an INHERITED field and must be routed into the parent subobject.
const EXTENDS: &str = "
structure P where
  p1 : Nat

structure Q extends P where
  q1 : Nat
";

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
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

#[test]
fn test_struct_instance_pattern_named_field_binds_that_field() {
    let src = format!(
        "{FOO}
def first : Foo -> Nat := fun | {{ a := x, .. }} => x
def second : Foo -> Nat := fun | {{ b := y, .. }} => y
theorem first_pin : first ⟨1, 2⟩ = 1 := rfl
theorem second_pin : second ⟨1, 2⟩ = 2 := rfl
"
    );
    elaborate_module(&src).expect("a `{ field := p, .. }` pattern must parse and elaborate");
}

/// Naming every field needs no `..`.
///
/// The body is PARENTHESISED on purpose, and the reason is a pre-existing
/// parser limitation that has nothing to do with this pattern:
/// `Parser::lambda_arm_expr` (`crates/clean-parser/src/grammar/expr_lambda_let.rs`)
/// parses a `fun | p => …` arm body as ONE atom plus projections, saying so in
/// its own comment ("Full applications would need layout information"), so a
/// bare `Nat.add x y` body leaves `x y` behind for the enclosing `app_expr` to
/// read as arguments of the lambda itself. Measured on `main` at this
/// package's merge base as well as here, for a `fun | n => Nat.add n n` with no
/// structure pattern anywhere in it — see
/// `test_pattern_lambda_arm_body_application_is_a_pre_existing_parser_gap`.
#[test]
fn test_struct_instance_pattern_every_field_without_ellipsis_elaborates() {
    let src = format!(
        "{FOO}
def sum : Foo -> Nat := fun | {{ a := x, b := y }} => (Nat.add x y)
theorem sum_pin : sum ⟨1, 2⟩ = 3 := rfl
"
    );
    elaborate_module(&src)
        .expect("naming every field needs no `..` and must bind the fields in order");
}

/// The same two-field binding through a `match`, where the arm body needs no
/// parentheses. This is the arm the Mathlib rows actually take.
#[test]
fn test_struct_instance_pattern_two_fields_in_a_match_arm_bind_in_order() {
    let src = format!(
        "{FOO}
def sumMatch (f : Foo) : Nat := match f with | {{ a := x, b := y }} => Nat.add x y
theorem sumMatch_pin : sumMatch ⟨1, 2⟩ = 3 := rfl
theorem sumMatch_pin2 : sumMatch ⟨10, 1⟩ = 11 := rfl
"
    );
    elaborate_module(&src).expect("two named fields must bind their OWN slots, in order");
}

#[test]
fn test_struct_instance_pattern_bare_ident_field_abbreviates_itself() {
    // `{ a }` ≡ `{ a := a }`, as in a structure LITERAL.
    let src = format!(
        "{FOO}
def viaAbbrev : Foo -> Nat := fun | {{ a, .. }} => a
theorem viaAbbrev_pin : viaAbbrev ⟨7, 2⟩ = 7 := rfl
"
    );
    elaborate_module(&src).expect("a bare-ident field abbreviation must bind that field");
}

#[test]
fn test_struct_instance_pattern_in_match_arm_elaborates() {
    let src = format!(
        "{FOO}
def viaMatch (f : Foo) : Nat :=
  match f with
  | {{ a := x, .. }} => x
theorem viaMatch_pin : viaMatch ⟨5, 6⟩ = 5 := rfl
"
    );
    elaborate_module(&src).expect("a `{ … }` pattern must work in a `match` arm too");
}

#[test]
fn test_struct_instance_pattern_inherited_field_routes_into_parent() {
    let src = format!(
        "{EXTENDS}
def parentField : Q -> Nat := fun | {{ p1 := n, .. }} => n
theorem parentField_pin : parentField ⟨⟨3⟩, 4⟩ = 3 := rfl
"
    );
    elaborate_module(&src)
        .expect("a field inherited through `extends` must route into the parent subobject");
}

#[test]
fn test_struct_instance_pattern_child_and_parent_fields_together() {
    let src = format!(
        "{EXTENDS}
def both : Q -> Nat := fun | {{ p1 := n, q1 := m, .. }} => (Nat.add n m)
theorem both_pin : both ⟨⟨3⟩, 4⟩ = 7 := rfl
"
    );
    elaborate_module(&src).expect("a child field and an inherited field must coexist");
}

#[test]
fn test_struct_instance_pattern_unknown_field_is_refused() {
    let src = format!(
        "{FOO}
def bad : Foo -> Nat := fun | {{ nosuch := x, .. }} => x
"
    );
    let err = elaborate_module(&src)
        .expect_err("a field the structure does not have must be refused, never wildcarded");
    assert!(
        err.contains("nosuch"),
        "the refusal must name the field; got: {err}"
    );
}

#[test]
fn test_struct_instance_pattern_missing_field_without_ellipsis_is_refused() {
    let src = format!(
        "{FOO}
def bad : Foo -> Nat := fun | {{ a := x }} => x
"
    );
    let err = elaborate_module(&src)
        .expect_err("omitting a field with no `..` must be refused, as a literal's would be");
    assert!(
        err.contains('b'),
        "the refusal must name the missing field; got: {err}"
    );
}

#[test]
fn test_struct_instance_pattern_duplicate_field_is_refused() {
    let src = format!(
        "{FOO}
def bad : Foo -> Nat := fun | {{ a := x, a := y, .. }} => x
"
    );
    elaborate_module(&src)
        .expect_err("naming one field twice must be refused, never silently dropped");
}

#[test]
fn test_struct_instance_pattern_with_source_is_refused() {
    // Lean: "Invalid struct instance pattern: `with` is not allowed in
    // patterns" (Lean/Elab/PatternVar.lean:306-307).
    let src = format!(
        "{FOO}
def bad : Foo -> Nat := fun | {{ f with a := x }} => x
"
    );
    elaborate_module(&src).expect_err("a `with` SOURCE is not a pattern and must be refused");
}

#[test]
fn test_struct_instance_pattern_ascription_naming_another_structure_is_refused() {
    let src = format!(
        "{FOO}{EXTENDS}
def bad : Foo -> Nat := fun | {{ a := x, .. : Q }} => x
"
    );
    elaborate_module(&src)
        .expect_err("an ascription naming a different structure must not be ignored");
}

#[test]
fn test_struct_instance_pattern_ascription_naming_the_structure_elaborates() {
    let src = format!(
        "{FOO}
def viaAscription : Foo -> Nat := fun | {{ a := x, .. : Foo }} => x
theorem viaAscription_pin : viaAscription ⟨9, 2⟩ = 9 := rfl
"
    );
    elaborate_module(&src).expect("`{ … : S }` naming the scrutinee's own structure must work");
}

/// CONTROL: the anonymous-constructor pattern keeps its `Prod.mk` right-nesting
/// (closed class 15 is built on it) and the `{` arm must not have disturbed it.
#[test]
fn test_anonymous_ctor_pattern_still_binds_fields_positionally() {
    let src = format!(
        "{FOO}
def viaAnon : Foo -> Nat := fun | ⟨x, _⟩ => x
theorem viaAnon_pin : viaAnon ⟨4, 5⟩ = 4 := rfl
"
    );
    elaborate_module(&src).expect("the ⟨…⟩ pattern must be unaffected by the `{ … }` arm");
}

/// DELIBERATE, MEASURED DIVERGENCE, in the refusing direction.
///
/// For a field carrying a DEFAULT, Lean materialises the default VALUE as the
/// pattern at that slot: `structure D where a : Nat; b : Nat := 5` with
/// `fun | { a := x } => x` elaborates to `D.mk x 5`, and pinned lean
/// v4.30.0-rc2 then reports the match NON-EXHAUSTIVE ("Missing cases:
/// (D.mk _ Nat.zero) …"). Both spellings are errors; Clean's is the one that
/// cannot silently change which values the arm matches, so the omission is
/// refused rather than filled with a pattern nobody wrote.
#[test]
fn test_struct_instance_pattern_defaulted_field_omission_is_refused() {
    let src = "
structure D where
  a : Nat
  b : Nat := 5

def usesDefault : D -> Nat := fun | { a := x } => x
";
    elaborate_module(src)
        .expect_err("omitting a DEFAULTED field with no `..` is refused, never filled");
}

/// PIN, PRE-EXISTING AND NOT THIS PACKAGE'S: a `fun | p => …` arm body is
/// parsed as one ATOM plus projections, so an unparenthesised application body
/// is cut short and its remaining tokens are read as arguments of the LAMBDA.
/// `Parser::lambda_arm_expr` says so itself ("Full applications would need
/// layout information to disambiguate"); Lean's `matchAlts` bounds the body by
/// LAYOUT instead and accepts the whole application.
///
/// Measured at this package's merge base with no structure pattern involved:
/// `def pI : Nat -> Nat := fun | n => Nat.add n n` fails "Unknown identifier:
/// n" — the `n`s that were meant to be the body's arguments become arguments of
/// `fun | n => Nat.add`, where nothing binds them. The `match` spelling of the
/// same body passes, which is what localises the gap to this one function.
///
/// TARGET ASSERTION: the day the arm body is parsed by layout, the first arm
/// here starts passing and this pin must be inverted.
#[test]
fn test_pattern_lambda_arm_body_application_is_a_pre_existing_parser_gap() {
    elaborate_module("def pI : Nat -> Nat := fun | n => Nat.add n n\n")
        .expect_err("an unparenthesised application arm body is cut short today");
    // CONTROLS: the two spellings that DO work, so the pin names the parser's
    // arm-body bound and not the elaborator or this package's pattern arm.
    elaborate_module("def pI : Nat -> Nat := fun | n => (Nat.add n n)\n")
        .expect("a parenthesised body is one atom and parses");
    elaborate_module("def pI (n : Nat) : Nat := match n with | n => Nat.add n n\n")
        .expect("the `match` arm body is bounded by layout and takes the application");
}

/// A `{ … }` pattern NESTED inside another constructor pattern — `some { a :=
/// x, .. }`. Pinned lean accepts it (measured), and the field-type recursion in
/// `normalize_match_pattern_names_inner` is what carries it.
#[test]
fn test_struct_instance_pattern_nested_in_a_constructor_pattern() {
    let src = format!(
        "{FOO}
def nested : Option Foo -> Nat := fun | some {{ a := x, .. }} => x | none => 0
theorem nested_pin : nested (some ⟨3, 4⟩) = 3 := rfl
"
    );
    elaborate_module(&src).expect("a `{ … }` pattern nested under `some` must elaborate");
}

// ---------------------------------------------------------------------------
// ADVERSARIAL REVIEW ADDITIONS (W3E review pass)
//
// Every expectation below was ground-truthed against the pinned binary
// `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean` on the SAME
// source shape before it was written here; the measured Lean output is quoted
// in each test's doc comment.
// ---------------------------------------------------------------------------

/// A three-level hierarchy, so an inherited field has to be routed twice.
const DEEP: &str = "
structure G where
  g1 : Nat

structure P extends G where
  p1 : Nat

structure C extends P where
  c1 : Nat
";

/// THE PRODUCTION SHAPE, which no test in this file reached: Mathlib writes
/// `Preorder.toLE_injective` and `LinearOrder.toPartialOrder_injective` as a
/// SINGLE arm over TWO positions —
///
/// ```lean
/// fun
/// | { lt := A_lt, .. },
///   { lt := B_lt, .. } => by …
/// ```
///
/// — which the parser desugars through the interleaved `_dxN` nest (closed
/// class 15), a different path from the one-position arm every other test here
/// takes. Pinned lean accepts the analogue and `example : pick ⟨1,2⟩ ⟨3,4⟩ = 5
/// := rfl` closes, so the value pin below is Lean's own answer.
#[test]
fn test_struct_instance_pattern_two_positions_one_arm_is_the_mathlib_shape() {
    let src = format!(
        "{FOO}
def pick : Foo -> Foo -> Nat := fun
  | {{ a := x, .. }},
    {{ b := y, .. }} => (Nat.add x y)
theorem pick_pin : pick ⟨1, 2⟩ ⟨3, 4⟩ = 5 := rfl
"
    );
    elaborate_module(&src).expect(
        "the two-position single-arm shape both Mathlib rows are written in must elaborate",
    );
}

/// The same two positions written with Mathlib's COMMA-LESS field layout
/// (`Mathlib/Order/Basic.lean:455-459` puts `toDecidableLT := …` and
/// `min := …` on consecutive lines with no comma). The parser's
/// `in_struct_pattern_field` boundary is what makes the second field's NAME
/// stop the first field's value; the `rfl` pin is what proves the boundary fell
/// in the right place rather than merely somewhere.
#[test]
fn test_struct_instance_pattern_two_positions_comma_less_fields_bind_correctly() {
    let src = format!(
        "{FOO}
def pick2 : Foo -> Foo -> Nat := fun
  | {{ a := x
       b := y }},
    {{ a := z
       b := w }} => (Nat.add x w)
theorem pick2_pin : pick2 ⟨1, 2⟩ ⟨3, 4⟩ = 5 := rfl
"
    );
    elaborate_module(&src)
        .expect("comma-less fields in a two-position arm must bind to their own names");
}

/// MEASURED DIVERGENCE, REPAIRED IN THIS REVIEW: the `..` must travel DOWN into
/// a parent subobject.
///
/// Pinned lean v4.30.0-rc2, measured on exactly this shape:
///
/// ```lean
/// structure P where p1 : Nat; p2 : Nat
/// structure C extends P where c1 : Nat
/// def f : C → Nat | { p1 := x, c1 := y } => x + y
/// -- error: Fields missing: `p2`
/// ```
///
/// The first landing built the parent subobject with `ellipsis = true`
/// unconditionally ("the child literal never claims to name them"), so Clean
/// ACCEPTED this and silently wildcarded `p2` — a pattern matching values it
/// was not written for, in the one direction a review of a pattern grammar
/// exists to catch. Flattened structure-instance notation does claim the
/// parent's fields: that is what flattening means.
#[test]
fn test_struct_instance_pattern_inherited_field_omitted_without_ellipsis_is_refused() {
    let src = "
structure P2 where
  p1 : Nat
  p2 : Nat

structure C2 extends P2 where
  c1 : Nat

def bad : C2 -> Nat := fun | { p1 := x, c1 := y } => x
";
    let err = elaborate_module(src).expect_err(
        "an unnamed INHERITED field with no `..` is missing, exactly as a direct one is",
    );
    assert!(
        err.contains("p2"),
        "the refusal must name the missing inherited field; got: {err}"
    );
    // CONTROL: with `..` the same pattern is accepted and binds `p1`.
    let ok = "
structure P2 where
  p1 : Nat
  p2 : Nat

structure C2 extends P2 where
  c1 : Nat

def good : C2 -> Nat := fun | { p1 := x, c1 := y, .. } => x
theorem good_pin : good ⟨⟨3, 4⟩, 5⟩ = 3 := rfl
";
    elaborate_module(ok).expect("`..` still wildcards the unnamed inherited field");
}

/// The same requirement two levels deep. Pinned lean on the `DEEP` hierarchy:
/// `| { g1 := x, c1 := y } => x + y` reports "Fields missing: `p1`", and
/// `| { c1 := y } => y` reports "Fields missing: `g1`, `p1`" — so the
/// obligation is RECURSIVE, not one level of routing.
#[test]
fn test_struct_instance_pattern_grandparent_routing_still_requires_the_middle_field() {
    let missing_middle = format!(
        "{DEEP}
def bad : C -> Nat := fun | {{ g1 := x, c1 := y }} => x
"
    );
    let err = elaborate_module(&missing_middle)
        .expect_err("`p1` is still missing when only `g1` and `c1` are named");
    assert!(
        err.contains("p1"),
        "the refusal must name the middle structure's field; got: {err}"
    );

    let all_named = format!(
        "{DEEP}
def deep : C -> Nat := fun | {{ g1 := x, p1 := z, c1 := y }} => (Nat.add x z)
theorem deep_pin : deep ⟨⟨⟨1⟩, 2⟩, 3⟩ = 3 := rfl
"
    );
    elaborate_module(&all_named)
        .expect("naming every flattened field two levels down must elaborate and bind in order");

    let with_ellipsis = format!(
        "{DEEP}
def deepDots : C -> Nat := fun | {{ g1 := x, .. }} => x
theorem deepDots_pin : deepDots ⟨⟨⟨7⟩, 2⟩, 3⟩ = 7 := rfl
"
    );
    elaborate_module(&with_ellipsis)
        .expect("`..` reaches the grandparent slot the child never names");
}

/// Naming the parent SUBOBJECT directly is Lean-legal and needs no `..`:
/// measured, `| { toP := q, c1 := y } => q.p1 + y` elaborates at the pin. And
/// naming the subobject AND one of its flattened fields is an error there —
/// "field `p1` has already been specified" — which Clean must also refuse
/// rather than silently letting one overwrite the other.
#[test]
fn test_struct_instance_pattern_subobject_named_directly_and_its_duplicate() {
    let direct = format!(
        "{DEEP}
def viaSub : C -> Nat := fun | {{ toP := q, c1 := y }} => (Nat.add q.p1 y)
theorem viaSub_pin : viaSub ⟨⟨⟨1⟩, 2⟩, 3⟩ = 5 := rfl
"
    );
    elaborate_module(&direct)
        .expect("a parent subobject named directly fills its slot with no `..` needed");

    let both = format!(
        "{DEEP}
def clash : C -> Nat := fun | {{ toP := q, p1 := z, c1 := y }} => z
"
    );
    elaborate_module(&both).expect_err(
        "naming the subobject and one of its flattened fields is `already specified` in Lean",
    );
}

/// `{ }` with no field and no `..` is a PARSE success and an elaboration
/// failure in Lean ("Fields missing: `a`, `b`"), and `{ .. }` is accepted.
/// Both are boundary shapes of the new field loop: the first exercises its
/// immediate `RBrace` break, the second its `DotDot` break.
#[test]
fn test_struct_instance_pattern_empty_braces_boundaries() {
    let empty = format!(
        "{FOO}
def emptyPat : Foo -> Nat := fun | {{ }} => 0
"
    );
    let err = elaborate_module(&empty)
        .expect_err("`{ }` names no field and omits `..`, so every field is missing");
    assert!(
        err.to_lowercase().contains("field"),
        "the refusal should be the missing-field one and name what is missing; got: {err}"
    );

    let dots = format!(
        "{FOO}
def dotsOnly : Foo -> Nat := fun | {{ .. }} => 0
theorem dotsOnly_pin : dotsOnly ⟨1, 2⟩ = 0 := rfl
"
    );
    elaborate_module(&dots).expect("`{ .. }` is an all-wildcard pattern");
}

/// A `{ … }` pattern inside a `{ … }` pattern's field value — the recursion
/// `struct_instance_pattern` makes into itself, and the save/restore of
/// `in_struct_pattern_field` around a nested value. The `rfl` pin is what
/// proves the inner field landed in the inner slot.
#[test]
fn test_struct_instance_pattern_nested_inside_a_field_value() {
    let src = format!(
        "{DEEP}
def nestedField : C -> Nat := fun | {{ toP := {{ p1 := z, .. }}, .. }} => z
theorem nestedField_pin : nestedField ⟨⟨⟨1⟩, 9⟩, 3⟩ = 9 := rfl
"
    );
    elaborate_module(&src)
        .expect("a `{ … }` pattern as another `{ … }` pattern's field value must elaborate");
}

/// A trailing comma after `..` is a PARSE ERROR in Lean ("unexpected token
/// ','; expected '}'"), while a trailing comma after a FIELD is fine (measured:
/// `{ a := x, }` parses and only then reports the missing `b`). The new loop
/// must agree in both directions, because `eat(&Comma)` after every field is
/// what makes the separator optional.
#[test]
fn test_struct_instance_pattern_trailing_comma_boundaries_match_lean() {
    let after_dots = format!(
        "{FOO}
def bad : Foo -> Nat := fun | {{ a := x, .. , }} => x
"
    );
    elaborate_module(&after_dots).expect_err("a comma after `..` is a parse error in Lean too");

    let after_field = format!(
        "{FOO}
def trailing : Foo -> Nat := fun | {{ a := x, b := y, }} => x
theorem trailing_pin : trailing ⟨1, 2⟩ = 1 := rfl
"
    );
    elaborate_module(&after_field)
        .expect("a trailing comma after the last FIELD is accepted, as it is in Lean");
}

/// The `in_struct_pattern_field` guard must be RESTORED, not merely set: a
/// constructor pattern written AFTER a structure pattern in the same arm still
/// takes its arguments, and an argument followed by `:=` outside a field value
/// (`let Foo.mk x := e`) is still an argument.
#[test]
fn test_struct_instance_pattern_field_boundary_guard_is_restored() {
    let src = format!(
        "{FOO}
def after : Foo -> Option Foo -> Nat := fun
  | {{ a := x, .. }}, some {{ b := y, .. }} => (Nat.add x y)
  | {{ a := x, .. }}, none => x
theorem after_pin : after ⟨1, 2⟩ (some ⟨3, 4⟩) = 5 := rfl
theorem after_none_pin : after ⟨1, 2⟩ none = 1 := rfl
"
    );
    elaborate_module(&src)
        .expect("a constructor pattern after a `{ … }` pattern still takes its argument");
}

/// A multi-constructor inductive has no `{ … }` form at all — pinned lean
/// reports that the expected type is not a structure. Clean must refuse rather
/// than pick a constructor.
#[test]
fn test_struct_instance_pattern_against_a_multi_constructor_inductive_is_refused() {
    let src = "
inductive Two where
  | one (a : Nat)
  | two (b : Nat)

def bad : Two -> Nat := fun | { a := x, .. } => x
";
    elaborate_module(src)
        .expect_err("a `{ … }` pattern against a multi-constructor inductive must be refused");
}

/// The `{ … : S }` ascription is compared by NAME COMPONENTS, not by display
/// string. Inside `namespace N` the structure is registered as `N.S` and the
/// abbreviated `S` must still match — pinned lean accepts
/// `fun | { a := x, .. : S } => x` there (measured) — while a spelling that is
/// merely a textual suffix of the structure's name is not the same name.
#[test]
fn test_struct_instance_pattern_ascription_matches_by_components_not_by_suffix() {
    let src = "
namespace N
structure S where
  a : Nat
  b : Nat

def viaAbbrev : S -> Nat := fun | { a := x, .. : S } => x
theorem viaAbbrev_pin : viaAbbrev ⟨1, 2⟩ = 1 := rfl
end N
";
    elaborate_module(src)
        .expect("a namespace-abbreviated ascription names the same structure and is accepted");
}

/// AN IMPLICIT constructor field is MATCHED in a pattern, not inferred — and
/// the class is UNREACHABLE in Clean today because the structure that would
/// carry it does not parse. Both halves are measured.
///
/// Pinned lean v4.30.0-rc2, on a structure with one implicit and one explicit
/// field:
///
/// ```lean
/// structure S where
///   mk :: {n : Nat} (m : Nat)
/// def g : S → Nat := fun | { m := y } => y
/// -- error: Fields missing: `n`
/// def f : S → Nat := fun | { n := x, m := y } => x + y   -- accepted
/// ```
///
/// So a pattern must NAME an implicit field: it is inferred in a structure
/// LITERAL and matched in a PATTERN. Clean cannot express the structure at all
/// — an implicit binder in a `mk ::` constructor signature dies in parser
/// recovery, measured below and pre-existing (the `mk :: (beq : …)` explicit
/// form in `congr_struct_eta_e2e.rs` parses fine) — so no `{ … }` pattern can
/// reach the case yet.
///
/// The missing-field scan in `build_struct_instance_ctor_pattern` nevertheless
/// covers EVERY slot rather than only `BinderInfo::Default` ones, so the day
/// the parser accepts the declaration the field cannot be silently wildcarded.
///
/// TARGET ASSERTION: the day `mk :: {n : Nat} (m : Nat)` parses, this
/// `expect_err` stops seeing a parse error and must be rewritten to assert the
/// two Lean behaviours above — the omission refused by NAME, the naming
/// accepted with a `rfl` value pin.
#[test]
fn test_struct_instance_pattern_implicit_constructor_field_is_unreachable_today() {
    let omitted = "
structure WithImplicit where
  mk :: {n : Nat} (m : Nat)

def bad : WithImplicit -> Nat := fun | { m := y } => y
";
    let err = elaborate_module(omitted)
        .expect_err("the declaration itself does not parse in Clean today");
    assert!(
        err.contains("parser recovery") || err.contains("Parse error"),
        "the refusal today is the PARSER's, not the missing-field scan's; got: {err}"
    );

    // CONTROL: the same structure with the field EXPLICIT parses and its
    // `{ … }` pattern behaves, so the pin names the implicit binder and not the
    // `mk ::` constructor syntax.
    let explicit = "
structure WithExplicit where
  mk :: (n : Nat) (m : Nat)

def ok : WithExplicit -> Nat := fun | { m := y, .. } => y
theorem ok_pin : ok ⟨1, 2⟩ = 2 := rfl
";
    elaborate_module(explicit)
        .expect("the explicit-binder spelling of the same declaration parses and elaborates");
}

/// A MULTI-SCRUTINEE `match a, b with | { … }, { … } => …` — the same two
/// positions as the Mathlib rows but through the `match` elaborator rather than
/// the pattern-lambda desugaring, so the two paths are pinned separately.
/// Accepted at the pin, with `m2 ⟨1,2⟩ ⟨3,4⟩ = 5` closing by `rfl` (measured).
#[test]
fn test_struct_instance_pattern_two_scrutinee_match_binds_each_position() {
    let src = format!(
        "{FOO}
def m2 (p : Foo) (q : Foo) : Nat := match p, q with
  | {{ a := x, .. }}, {{ b := y, .. }} => Nat.add x y
theorem m2_pin : m2 ⟨1, 2⟩ ⟨3, 4⟩ = 5 := rfl
"
    );
    elaborate_module(&src)
        .expect("a two-scrutinee match over two `{ … }` patterns must bind each position");
}
