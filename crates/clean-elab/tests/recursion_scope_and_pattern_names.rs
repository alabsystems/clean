// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! False theorems measured 2026-09-25 against Lean 4.8.0, and their fixes.
//!
//! * RECURSION SCOPE. `T.rec` re-runs only what sits below the match on the
//!   decreasing argument. A minor that read a value bound OUTSIDE that match
//!   from the recursive parameters (an outer `let`, an enclosing case split on
//!   another parameter) reused it at every recursive call: `h 2 = 6` for
//!   `let q := b; match b with | succ y => h y + q | zero => q` (Lean: 3), and
//!   `f 1 2 = 0` for `| 0, y => y | x+1, y+1 => f (x-2) y | x+1, 0 => 0`,
//!   whose equation lowering matched `x` first and recursed on `y` inside it
//!   (Lean: 1). Such a lowering is now refused
//!   (`check_recursive_minors_closed`), and the equation / `match x, y`
//!   normalizers put the decreasing column outermost so it lowers correctly.
//!   Since 2026-09-26 the outer `let`/`fun`/case split is moved into the
//!   match's arms first (`structural::hoist_recursive_match`), so these
//!   definitions compute Lean's value; the check stays for what that declines.
//! * CAPTURE. With the decreasing column first, a constructor field bound
//!   under its row's own name (`y` in `y+1`) shadowed the scrutinee `y` that
//!   an earlier row (`| 0, y => y + 10`) re-binds below it: `b 1 2 = 10`
//!   (Lean: 11).
//! * PATTERN NAMES (class R). A bare pattern identifier that ordinary name
//!   resolution does not find is a VARIABLE in Lean 4; Clean resolved it
//!   through the scrutinee type's namespace (`c` ↦ `U.c`), so `q (some U.a)
//!   = 1` held for `| some c => 0 | _ => 1` (Lean: 0). The two readings
//!   differ, so such a pattern is now refused; `.c`, `U.c`, `open U` and
//!   `namespace U` spellings are unaffected.
//! * NON-LINEAR PATTERNS (class N). `| some x, some x => …` is refused, as
//!   in Lean.
//! * FIRST MATCH. The recursive lowering let a constructor arm AFTER a
//!   catch-all win for that constructor: `g 2 = 21` for `| x => x + 1 |
//!   Nat.succ k => g k + 10` (source order, and the non-recursive lowering,
//!   give 3).
//!
//! Every computation registers the TRUE equation (axiom-free) and refuses the
//! FALSE one. The generated battery at the end decides truth with an
//! evaluator written here, not with Clean.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => {
                for result in results {
                    failures(result)?;
                }
                Ok(())
            }
            ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
            _ => Ok(()),
        }
    }
    let mut context = FileContext::new();
    for decl in parse_file(source).map_err(|error| format!("parse error: {error}"))? {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register(env, &processed)
            .map_err(|error| format!("elaborate/kernel-check error: {error}"))?;
        failures(&result)?;
    }
    Ok(())
}

#[test]
fn namespace_recursive_receiver_uses_the_structural_child_and_updated_parameters() {
    let mut env = Environment::with_prelude();
    let source = r#"
namespace Probe
inductive T where
  | lit (n : Nat)
  | child (sub : T)
  | throughName (sub : T)
namespace T
def scan (depth under : Nat) : T → Nat
  | .lit n => under + n + depth
  | .child sub => sub.scan depth (under + 1)
  | .throughName sub => T.scan depth (under + 2) sub
end T
end Probe
theorem methodSteps : Probe.T.scan 3 4 (.child (.throughName (.lit 1))) = 11 := rfl
"#;
    register(&mut env, source).expect("both self-call spellings must compute");
    let dependencies = env
        .axiom_deps(&Name::from_string("methodSteps"))
        .expect("registered method-step equation");
    assert!(dependencies.is_empty(), "{dependencies:?}");

    let wrong =
        "theorem badMethodSteps : Probe.T.scan 3 4 (.child (.throughName (.lit 1))) = 10 := rfl";
    let error = register(&mut env, wrong).expect_err("wrong accumulator result must fail");
    assert!(error.contains("Type mismatch"), "{error}");
    assert!(env
        .get_const(&Name::from_string("badMethodSteps"))
        .is_none());

    let nondecreasing = r#"
namespace Probe.T
def nondecreasing (depth under : Nat) : Probe.T → Nat
  | .lit n => under + n + depth
  | .child sub =>
      let whole := Probe.T.child sub
      whole.nondecreasing depth (under + 1)
  | .throughName sub => nondecreasing depth under sub
end Probe.T
"#;
    let error = register(&mut env, nondecreasing).expect_err("rebuilt receiver must fail");
    assert!(
        error.contains("nondecreasing") && error.contains("recurs"),
        "{error}"
    );
    assert!(env
        .get_const(&Name::from_string("Probe.T.nondecreasing"))
        .is_none());
}

#[test]
fn nested_list_suffix_checks_the_original_sha_words_equations() {
    let mut env = Environment::with_prelude();
    let source = include_str!("recursion_scope_and_pattern_names/sha_words.lean");
    register(&mut env, source).expect(
        "the generated function must satisfy its equations and equal the explicit recursor",
    );
    for law in [
        "law_nil",
        "law_one",
        "law_two",
        "law_three",
        "law_chunk",
        "actual_compiler_window",
    ] {
        let dependencies = env
            .axiom_deps(&Name::from_string(law))
            .expect("registered source equation");
        assert!(
            dependencies.is_empty(),
            "{law} unexpectedly uses {dependencies:?}"
        );
    }
    let wrong_suffix = source.replace(":: previous.2.2.2", ":: previous.2.2.1");
    let mut changed_env = Environment::with_prelude();
    let error = register(&mut changed_env, &wrong_suffix)
        .expect_err("the altered recursor must fail the same universal equality");
    assert!(changed_env
        .get_const(&Name::from_string("law_chunk"))
        .is_some());
    assert!(changed_env
        .get_const(&Name::from_string("Scratch.result"))
        .is_some());
    assert!(changed_env
        .get_const(&Name::from_string("actual_compiler_window"))
        .is_none());
    assert!(
        error.contains("SemR.shaWords") && error.contains("Scratch.result"),
        "{error}"
    );
    assert!(error.contains("Type mismatch"), "{error}");
    register(
        &mut env,
        "theorem nested_sha_correct : SemR.shaWords [0,0,0,0,1,0,0,0] = [0,16777216] := rfl",
    )
    .expect("recursion must use the suffix after four heads");
    assert!(register(
        &mut env,
        "theorem nested_sha_incorrect : SemR.shaWords [0,0,0,0,1,0,0,0] = [0,65536] := rfl"
    )
    .is_err());
    assert!(env
        .get_const(&Name::from_string("nested_sha_incorrect"))
        .is_none());
}

#[test]
fn nested_list_suffix_respects_scopes_and_the_decrease() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
namespace Suffix
def a : Nat := 7
def f : List Nat → Nat
  | a :: b :: rest => a + b + f rest
  | _ => a
end Suffix
"#,
    )
    .expect("fallback names are resolved in their original scope");
    computation(&mut env, "nested_fallback", "Suffix.f [9]", 7, 9);
    computation(&mut env, "nested_two_heads", "Suffix.f [1, 2, 3]", 10, 6);
    for source in [
        "def sameList : List Nat → Nat | a :: b :: rest => sameList (a :: b :: rest) | _ => 0",
        "def duplicates : List Nat → Nat | a :: a :: rest => a + duplicates rest | _ => 0",
    ] {
        assert!(register(&mut env, source).is_err());
    }
}

#[test]
fn a_structurally_smaller_call_can_be_a_callback_or_fully_applied() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
namespace Weighted
def apply2 (f : Bool → Bool → Nat) (a b : Bool) : Nat := f a b
def result (m : Nat) : Nat → Bool → Bool → Nat
  | 0, a, _ => if a then m + 2 else m + 5
  | fuel + 1, true, b => 1 + apply2 (result m fuel) false b
  | fuel + 1, false, b => 3 + result m fuel true b
theorem partial_equation (m fuel : Nat) (b : Bool) :
    result m (fuel + 1) true b = 1 + result m fuel false b := rfl
theorem direct_equation (m fuel : Nat) (b : Bool) :
    result m (fuel + 1) false b = 3 + result m fuel true b := rfl
end Weighted
"#,
    )
    .expect("the resulting kernel term must satisfy both equations for every smaller fuel");
    computation(
        &mut env,
        "mixed_saturation_callback",
        "Weighted.result 4 1 true false",
        10,
        9,
    );
    computation(
        &mut env,
        "mixed_saturation_direct",
        "Weighted.result 4 1 false false",
        9,
        10,
    );
    for source in [
        "def bad (m : Nat) : Nat → Bool → Bool → Nat | 0, _, _ => m | n + 1, true, b => Weighted.apply2 (bad m (n + 1)) false b | n + 1, false, b => bad m n true b",
        "def escapes (m : Nat) : Nat → Bool → Bool → Nat | 0, _, _ => m | n + 1, a, b => (fun k => k (n + 1) a b) (escapes m)",
    ] {
        assert!(register(&mut env, source).is_err());
    }
}

/// `call = expected` must register axiom-free; `call = wrong` must be refused.
fn computation(env: &mut Environment, tag: &str, call: &str, expected: u64, wrong: u64) {
    assert_ne!(
        expected, wrong,
        "{tag}: a check needs a genuinely wrong value"
    );
    let good = format!("correct_{tag}");
    register(env, &format!("theorem {good} : {call} = {expected} := rfl"))
        .unwrap_or_else(|error| panic!("{call} = {expected} must hold: {error}"));
    let deps = env
        .axiom_deps(&Name::from_string(&good))
        .expect("registered theorem");
    assert!(
        deps.is_empty(),
        "{call}: computation depends on axioms: {deps:?}"
    );
    refused(env, tag, call, wrong);
}

/// `call = wrong` must be refused and leave nothing registered.
fn refused(env: &mut Environment, tag: &str, call: &str, wrong: u64) {
    let bad = format!("incorrect_{tag}");
    let error = register(env, &format!("theorem {bad} : {call} = {wrong} := rfl"))
        .expect_err(&format!("FALSE theorem accepted: {call} = {wrong}"));
    assert!(
        !error.contains("parse error"),
        "negative must parse: {error}"
    );
    assert!(
        env.get_const(&Name::from_string(&bad)).is_none(),
        "false theorem registered: {call} = {wrong}"
    );
}

/// A definition that must be refused as a whole, with `needle` in the error;
/// nothing named `name` may be registered.
fn def_refused(env: &mut Environment, name: &str, source: &str, needle: &str) {
    let error = register(env, source).expect_err(&format!("must be refused:\n{source}"));
    assert!(
        error.contains(needle),
        "{name}: refused for the wrong reason (want `{needle}`): {error}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "{name} was registered although refused"
    );
}

fn run(env: &mut Environment, prefix: &str, cases: &[(&str, u64, u64)]) {
    for (id, (call, expected, wrong)) in cases.iter().enumerate() {
        computation(env, &format!("{prefix}{id}"), call, *expected, *wrong);
    }
}

// Measured 2026-09-25: the recursor sat at the `match`, below the outer
// `let`/`have`/`fun`, so the IH reused the outer value (`x 2 = 6`; Lean 4.8.0:
// `x 2 = 3`), and such definitions were refused since. The context is now moved
// into the match's arms (`structural::hoist_recursive_match`, 2026-09-26), so
// the recursor computes the whole definition: each registers with Lean's value
// (checked with Lean 4.8.0), and the measured false value stays unprovable.
#[test]
fn rec_minor_reading_an_outer_let_or_binder_computes_leans_value() {
    let mut env = Environment::with_prelude();
    for (name, source, cases) in [
        (
            "hLet",
            "def hLet (b : Nat) : Nat :=\n  let q := b\n  match b with\n    | Nat.succ y => hLet y + q\n    | Nat.zero => q",
            [("hLet 2", 3, 6), ("hLet 0", 0, 1)],
        ),
        (
            "hHave",
            "def hHave (b : Nat) : Nat :=\n  have q : Nat := b\n  match b with\n    | Nat.succ y => hHave y + q\n    | Nat.zero => q",
            [("hHave 2", 3, 6), ("hHave 0", 0, 1)],
        ),
        (
            "hFun",
            "def hFun (b : Nat) : Nat :=\n  (fun q => match b with\n    | Nat.succ y => hFun y + q\n    | Nat.zero => q) b",
            [("hFun 2", 3, 6), ("hFun 0", 0, 1)],
        ),
        // A generalized (non-decreasing) parameter read through an outer let.
        (
            "hAcc",
            "def hAcc (b acc : Nat) : Nat :=\n  let q := acc\n  match b with\n    | Nat.succ y => hAcc y (acc + 1) + q\n    | Nat.zero => q",
            [("hAcc 2 0", 3, 0), ("hAcc 3 1", 10, 4)],
        ),
    ] {
        register(&mut env, source).unwrap_or_else(|error| panic!("{name}: {error}"));
        run(&mut env, name, &cases);
    }
}

// Measured 2026-09-25: the recursion on `b` sat inside the case split on `a`,
// so the IH reused the outer `x` and ignored the call's `0` (`c 1 2 = 200`;
// Lean 4.8.0: 111), and the definition was refused since. The match on `b` is
// now the whole body, the case split on `a` re-runs at every level.
#[test]
fn rec_nested_inside_a_case_split_on_another_parameter_computes_leans_value() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "def cNest (a b : Nat) : Nat :=\n  match a with\n  | Nat.zero => b + 10\n  | Nat.succ x =>\n    match b with\n    | Nat.succ y => cNest 0 y + 100\n    | Nat.zero => x",
    )
    .expect("cNest recurses on `b`");
    run(
        &mut env,
        "cn",
        &[
            ("cNest 1 2", 111, 200),
            ("cNest 2 0", 1, 0),
            ("cNest 0 5", 15, 5),
        ],
    );
}

// Class (54)'s SILENT WRONG VALUE, measured 2026-09-25 through `clean run`:
// structural recursion whose recursive call CHANGES a non-decreasing
// constructor-pattern argument split that argument outside the recursor, so
// every level read the ORIGINAL fields -- `recFirst ⟨3,4⟩ 1` was 3 (Lean 4).
// Closed by 0ffcbd885 (the decreasing column lowered outermost) and
// 5809a76e8, and pinned here by VALUE, not by acceptance: each call registers
// Lean's value (pinned v4.30.0-rc2 `#eval`: [3, 4, 3, 4])
// axiom-free by `rfl`, and the value the defect computed stays unprovable.
// (The recFirst shape's lowering is also pinned by
// `tests_single_equation_lowering.rs`'s `pr` fixture.)
#[test]
fn rec_generalizing_a_constructor_argument_computes_leans_value() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "structure P2 where\n  a : Nat\n  b : Nat\n\
         def recFirst : P2 → Nat → Nat\n  \
         | ⟨x, _⟩, 0 => x\n  \
         | ⟨x, y⟩, n + 1 => recFirst ⟨y, x⟩ n",
    )
    .expect("recFirst elaborates");
    run(
        &mut env,
        "rf",
        &[
            ("recFirst ⟨3, 4⟩ 0", 3, 4),
            // the measured wrong value: 3
            ("recFirst ⟨3, 4⟩ 1", 4, 3),
            ("recFirst ⟨3, 4⟩ 2", 3, 4),
            ("recFirst ⟨3, 4⟩ 3", 4, 3),
        ],
    );
}

// OPEN, class (71) of docs/FRONTEND_CLASS_LEDGER.md, measured 2026-09-29: the
// same recursion over a THREE-field structure, whose anonymous-constructor
// pattern `⟨a, b, c⟩` sits in the non-decreasing column, is refused -- the
// recursive equation lowering reads the three components as nested `Prod.mk`.
// Pinned Lean v4.30.0-rc2 accepts it and computes `rot3 ⟨1, 2, 3⟩ 4 = 2`
// (`#eval` [1, 2, 3, 2] for n = 0, 1, 2, 4). A single-equation, a
// non-recursive two-column, and a `match` spelling of the same pattern all
// elaborate here; only the recursive lowering refuses. This fails the day it
// closes: replace it with `rfl` value pins then.
#[test]
fn rec_over_a_three_field_anonymous_constructor_pattern_is_refused_open_class_71() {
    let mut env = Environment::with_prelude();
    def_refused(
        &mut env,
        "rot3",
        "structure P3 where\n  a : Nat\n  b : Nat\n  c : Nat\n\
         def rot3 : P3 → Nat → Nat\n  \
         | ⟨a, _, _⟩, 0 => a\n  \
         | ⟨a, b, c⟩, n + 1 => rot3 ⟨b, c, a⟩ n",
        "expected constructor of P3, got constructor Prod.mk of Prod",
    );
}

#[test]
fn a_let_that_does_not_depend_on_the_parameters_is_still_admitted() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "def kConst (b : Nat) : Nat :=\n  let q := 5\n  match b with\n    | Nat.succ y => kConst y + q\n    | Nat.zero => q",
    )
    .expect("a parameter-free let is sound to reuse");
    run(&mut env, "kc", &[("kConst 2", 15, 11), ("kConst 0", 5, 6)]);
}

#[test]
fn decreasing_column_is_lowered_outermost() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        r#"
def f : Nat → Nat → Nat
  | 0,   y   => y
  | x+1, y+1 => f (x-2) y
  | x+1, 0   => 0
def a : Nat → Nat → Nat
  | Nat.zero, y => y + 10
  | Nat.succ x, Nat.succ y => a 0 y
  | Nat.succ x, Nat.zero => x
def q1 : Nat → Nat → Nat
  | 0, y => y + 10
  | x+1, y+1 => q1 (x) y
  | x+1, 0 => x
def q8 : Nat → Nat → Nat
  | 0, y => y + 10
  | x+1, y+1 => q8 (x*2) y
  | x+1, 0 => x
def b (x y : Nat) : Nat :=
  match x, y with
  | 0, y => y + 10
  | x+1, y+1 => b 0 y
  | x+1, 0 => x
"#,
    )
    .unwrap();
    run(
        &mut env,
        "dec",
        &[
            // Measured false on the previous lowering: `f 1 2 = 0`, `f 3 5 = 0`.
            ("f 1 2", 1, 0),
            ("f 3 5", 4, 0),
            ("f 0 7", 7, 0),
            // `a 1 2 = 0` was accepted on the base as well.
            ("a 1 2", 11, 0),
            ("a 3 0", 2, 11),
            ("q1 4 1", 2, 3),
            ("q1 2 3", 11, 12),
            ("q8 4 1", 5, 3),
            ("q8 3 3", 9, 12),
            // `match x, y with`: measured `b 1 2 = 0` before, and `10` once the
            // column was rotated without capture avoidance.
            ("b 1 2", 11, 0),
            ("b 1 2", 11, 10),
            ("b 2 0", 1, 10),
        ],
    );
}

#[test]
fn a_let_alias_of_a_constructor_field_keeps_its_induction_hypothesis() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "def hq (x y : Nat) : Nat :=\n  match y with\n  | Nat.succ yf =>\n    match x with\n    | Nat.zero => y + 10\n    | Nat.succ xf => let q := yf; hq 0 q\n  | Nat.zero => 0",
    )
    .expect("recursion through `let q := yf` is structural");
    run(&mut env, "alias", &[("hq 1 2", 11, 0), ("hq 0 3", 13, 11)]);
}

#[test]
fn bare_name_resolved_only_through_the_scrutinee_type_is_refused() {
    let mut env = Environment::with_prelude();
    register(&mut env, "inductive U where\n  | a : U\n  | c : U").unwrap();
    const AMBIGUOUS: &str = "is a pattern variable in Lean 4";
    // Each was a constructor test in Clean and a catch-all in Lean 4.8.0; the
    // FALSE `… (some U.a) = 1` / `… U.a = 1` was provable.
    for (name, source) in [
        ("q1", "def q1 : Option U → Nat\n  | some c => 0\n  | _ => 1"),
        ("q3", "def q3 (x : U) : Nat :=\n  match x with\n  | c => 0\n  | _ => 1"),
        ("z1", "def z1 : Option Nat → Nat\n  | some zero => 0\n  | _ => 1"),
        ("z2", "def z2 : Option (List Nat) → Nat\n  | some nil => 0\n  | _ => 1"),
        ("w2", "def w2 : Option U → Nat → Nat\n  | some c, 0 => 0\n  | _, _ => 1"),
        (
            "w1",
            "def w1 : Nat → Option U → Nat\n  | 0, some c => 0\n  | 0, _ => 1\n  | n + 1, x => w1 n x",
        ),
        (
            "w8",
            "def w8 (x : Option U) (y : Nat) : Nat :=\n  match x, y with\n  | some c, 0 => 0\n  | _, _ => 1",
        ),
    ] {
        def_refused(&mut env, name, source, AMBIGUOUS);
    }
    // The unambiguous spellings keep working, with the constructor reading.
    register(
        &mut env,
        r#"
def d1 : Option U → Nat
  | some .c => 0
  | _ => 1
def d2 : Option U → Nat
  | some U.c => 0
  | _ => 1
open U in
def d3 : Option U → Nat
  | some c => 0
  | _ => 1
namespace U
def d4 : Option U → Nat
  | some c => 0
  | _ => 1
end U
def d5 : Nat → Option U → Nat
  | 0, some .c => 0
  | 0, _ => 1
  | n + 1, x => d5 n x
"#,
    )
    .unwrap();
    run(
        &mut env,
        "spell",
        &[
            ("d1 (some U.a)", 1, 0),
            ("d1 (some U.c)", 0, 1),
            ("d2 (some U.a)", 1, 0),
            ("d3 (some U.a)", 1, 0),
            ("d3 (some U.c)", 0, 1),
            ("U.d4 (some U.a)", 1, 0),
            ("d5 2 (some U.a)", 1, 0),
            ("d5 2 (some U.c)", 0, 1),
        ],
    );
}

#[test]
fn a_variable_named_like_some_unrelated_constructor_is_a_variable() {
    let mut env = Environment::with_prelude();
    register(&mut env, "inductive V where\n  | p : V\n  | q : V").unwrap();
    // `p` names `V.p` and `zero` names `Nat.zero`, but neither is a
    // constructor of the field's type (`Nat`, `Option Nat`) nor resolves by
    // ordinary name resolution: Lean binds both. The previous lowering
    // refused both definitions.
    register(
        &mut env,
        r#"
def w5 : Nat → Option Nat → Nat
  | 0, some p => p + 1
  | 0, _ => 0
  | n + 1, x => w5 n x
def w7 : Nat → Option (Option Nat) → Nat
  | 0, some zero => 0
  | 0, _ => 1
  | n + 1, x => w7 n x
"#,
    )
    .unwrap();
    run(
        &mut env,
        "unrel",
        &[
            ("w5 1 (some 7)", 8, 0),
            ("w5 0 none", 0, 8),
            ("w7 0 (some (some 3))", 0, 1),
            ("w7 2 (none : Option (Option Nat))", 1, 0),
        ],
    );
}

#[test]
fn non_linear_patterns_are_refused() {
    let mut env = Environment::with_prelude();
    const NONLINEAR: &str = "occurred more than once";
    for (name, source) in [
        (
            "k11",
            "def k11 : Option Nat → Option Nat → Nat\n  | some x, some x => 0\n  | _, _ => 1",
        ),
        (
            "k12",
            "def k12 (a b : Nat) : Nat :=\n  match a, b with\n  | x, x => 0\n  | _, _ => 1",
        ),
        (
            "k13",
            "def k13 : Nat → Nat → Nat\n  | 0, y => y\n  | n + 1, n => k13 n n",
        ),
        (
            "k14",
            "def k14 (p : Nat × Nat) : Nat :=\n  match p with\n  | (x, x) => 0",
        ),
    ] {
        def_refused(&mut env, name, source, NONLINEAR);
    }
    // Or-alternatives bind their variables separately.
    register(
        &mut env,
        "def k15 (p : Option Nat) : Nat :=\n  match p with\n  | some 0 | none => 0\n  | some x => x",
    )
    .unwrap();
    run(
        &mut env,
        "or",
        &[("k15 (some 4)", 4, 0), ("k15 none", 0, 4)],
    );
}

/// An arm behind a catch-all is selected by no value: pinned Lean 4.8.0
/// refuses each of these definitions ("redundant alternative", measured
/// 2026-10-16), and so does Clean since round-5 lane D (G62, ledger (89)).
/// This test used to register them and check first-match values (measured
/// false before that: `g1 2 = 21`, `g3 2 = 21`, `g5 [1,2] = 2`).
#[test]
fn recursive_lowering_is_first_match_after_a_catch_all() {
    for source in [
        "def g1 : Nat → Nat\n  | x => x + 1\n  | Nat.succ k => g1 k + 10",
        "def g3 (n : Nat) : Nat :=\n  match n with\n  | x => x + 1\n  | Nat.succ k => g3 k + 10",
        "def g5 : List Nat → Nat\n  | x => 0\n  | a :: t => g5 t + 1",
    ] {
        let mut env = Environment::with_prelude();
        let err = register(&mut env, source).expect_err("Lean refuses an arm behind a catch-all");
        assert!(
            err.contains("redundant alternative"),
            "the refusal is Lean's redundancy: {err}\n{source}"
        );
    }
}

/// Deterministic generator (no external crates).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
}

/// Column pattern of a two-argument Nat equation: `0`, `k`, `v+1`, `_`, `v`.
#[derive(Clone, Copy)]
enum Pat {
    Lit(u64),
    Succ,
    Wild,
    Var,
}

/// A recursive-call argument: a literal, the row's structurally smaller
/// variable, one of the row's variables, or that plus/minus one.
#[derive(Clone, Copy)]
enum Arg {
    Lit(u64),
    Var(usize),
    Plus(usize),
    Minus(usize),
}

#[derive(Clone)]
struct Row {
    pats: [Pat; 2],
    call: Option<[Arg; 2]>,
    constant: u64,
}

fn var_name(row: usize, col: usize) -> String {
    format!("v{row}{col}")
}

fn pat_src(p: Pat, row: usize, col: usize) -> String {
    match p {
        Pat::Lit(k) => k.to_string(),
        Pat::Succ => format!("{}+1", var_name(row, col)),
        Pat::Wild => "_".into(),
        Pat::Var => var_name(row, col),
    }
}

fn arg_src(a: Arg, row: usize) -> String {
    match a {
        Arg::Lit(k) => k.to_string(),
        Arg::Var(col) => var_name(row, col),
        Arg::Plus(col) => format!("({} + 1)", var_name(row, col)),
        Arg::Minus(col) => format!("({} - 1)", var_name(row, col)),
    }
}

/// Bind a column: `Some(Some(v))` binds `v`, `Some(None)` matches without
/// binding, `None` fails.
fn bind(p: Pat, value: u64) -> Option<Option<u64>> {
    match p {
        Pat::Lit(k) => (value == k).then_some(None),
        Pat::Succ => (value >= 1).then(|| Some(value - 1)),
        Pat::Wild => Some(None),
        Pat::Var => Some(Some(value)),
    }
}

fn eval(rows: &[Row], x: u64, y: u64, fuel: &mut u32) -> Option<u64> {
    *fuel = fuel.checked_sub(1)?;
    for row in rows {
        let (Some(b0), Some(b1)) = (bind(row.pats[0], x), bind(row.pats[1], y)) else {
            continue;
        };
        let vars = [b0, b1];
        let arg = |a: Arg| -> Option<u64> {
            match a {
                Arg::Lit(k) => Some(k),
                Arg::Var(c) => vars[c],
                Arg::Plus(c) => vars[c].map(|v| v + 1),
                Arg::Minus(c) => vars[c].map(|v| v.saturating_sub(1)),
            }
        };
        return match row.call {
            None => Some(row.constant),
            Some([a0, a1]) => {
                let (v0, v1) = (arg(a0)?, arg(a1)?);
                Some(eval(rows, v0, v1, fuel)? + row.constant)
            }
        };
    }
    None
}

/// Which rows of `rows` are the first match for some `(x, y)`. Literals are
/// below 3, so `0..=3` stands for every `Nat` in each column (each larger
/// value matches exactly the patterns 3 does) and the answer is exact.
fn reachable_rows(rows: &[Row]) -> Vec<bool> {
    let mut reached = vec![false; rows.len()];
    for x in 0..=3 {
        for y in 0..=3 {
            if let Some(first) = rows
                .iter()
                .position(|row| bind(row.pats[0], x).is_some() && bind(row.pats[1], y).is_some())
            {
                reached[first] = true;
            }
        }
    }
    reached
}

fn has_unreachable_row(rows: &[Row]) -> bool {
    reachable_rows(rows).contains(&false)
}

/// Random rows for one definition (`dec` is the decreasing column), ending
/// in the catch-all `_, _`.
fn generate_rows(rng: &mut Lcg, dec: usize) -> Vec<Row> {
    let mut rows: Vec<Row> = Vec::new();
    for _ in 0..2 + rng.next(2) {
        let mut pats = [Pat::Wild; 2];
        for p in &mut pats {
            *p = match rng.next(4) {
                0 => Pat::Lit(rng.next(3)),
                1 => Pat::Succ,
                2 => Pat::Wild,
                _ => Pat::Var,
            };
        }
        let call = if matches!(pats[dec], Pat::Succ) && rng.next(3) != 0 {
            let other = 1 - dec;
            let mut args = [Arg::Lit(0); 2];
            args[dec] = Arg::Var(dec);
            let bound = matches!(pats[other], Pat::Succ | Pat::Var);
            args[other] = match rng.next(4) {
                0 => Arg::Lit(rng.next(4)),
                1 if bound => Arg::Var(other),
                2 if bound => Arg::Plus(other),
                3 if bound => Arg::Minus(other),
                _ => Arg::Lit(rng.next(4)),
            };
            Some(args)
        } else {
            None
        };
        rows.push(Row {
            pats,
            call,
            constant: rng.next(6),
        });
    }
    rows.push(Row {
        pats: [Pat::Wild; 2],
        call: None,
        constant: rng.next(6),
    });
    rows
}

/// The source of a generated definition, in equation or `match x, y` form.
fn rows_source(name: &str, rows: &[Row], match_form: bool) -> String {
    let mut src = if match_form {
        format!("def {name} (x y : Nat) : Nat :=\n  match x, y with\n")
    } else {
        format!("def {name} : Nat → Nat → Nat\n")
    };
    for (i, row) in rows.iter().enumerate() {
        let body = match row.call {
            None => row.constant.to_string(),
            Some([a0, a1]) => format!(
                "{name} {} {} + {}",
                arg_src(a0, i),
                arg_src(a1, i),
                row.constant
            ),
        };
        src.push_str(&format!(
            "  | {}, {} => {body}\n",
            pat_src(row.pats[0], i, 0),
            pat_src(row.pats[1], i, 1)
        ));
    }
    src
}

/// Two-argument recursive definitions in equation and `match x, y` form
/// whose recursive calls pass arbitrary values in the non-decreasing column.
/// A definition may be refused (loudly) — a refusal is never a false theorem
/// — but every theorem Clean accepts must agree with first-match evaluation,
/// and every false twin must be refused.
///
/// Only definitions Lean 4.8.0 accepts are measured: one with a row no value
/// reaches is "redundant alternative" there and has no value semantics. Each
/// such candidate is still elaborated, and Clean's verdict is checked, never
/// skipped:
///
/// * refused as a redundant alternative, with nothing registered;
/// * refused for another reason only if Clean also refuses the definition
///   with its unreachable rows removed (the refusal does not hide the row);
/// * accepted only as ledger class (89): a NON-recursive definition whose
///   rows test at most one column in equation form, and none in `match x, y`
///   form (a column is STRUCTURAL when some row matches it on a literal or
///   `v+1`). Those lower through a match that builds no decision tree. Its
///   value is then checked on every input of the exact domain against
///   first-match semantics, so that lowering's meaning stays pinned. Two
///   structural columns go through the equation matrix, one or more in
///   `match x, y` through the constructor-field split of the `Prod`
///   scrutinee, and a recursive definition through the recursive `Nat`
///   reading; each must refuse the row (`2cd5d8d5c`, `1c36cee62`).
///
/// At least one candidate must be refused as redundant, or the reason check
/// is vacuous; and a definition WITHOUT such a row must never be refused as
/// redundant.
#[test]
fn generated_recursive_call_battery_agrees_with_first_match_semantics() {
    let mut env = Environment::with_prelude();
    let mut rng = Lcg(0x5eed_2026_0925);
    let mut accepted_true = 0usize;
    let mut refused_false = 0usize;
    let mut redundant_candidates = 0usize;
    let mut refused_redundant = 0usize;
    for def_id in 0..160 {
        let dec = rng.next(2) as usize;
        let match_form = def_id % 2 == 1;
        let rows = loop {
            let rows = generate_rows(&mut rng, dec);
            if !has_unreachable_row(&rows) {
                break rows;
            }
            let name = format!("redundant{redundant_candidates}");
            let src = rows_source(&name, &rows, match_form);
            match register(&mut env, &src) {
                Err(error) if error.contains("redundant alternative") => {
                    assert!(
                        env.get_const(&Name::from_string(&name)).is_none(),
                        "refused yet registered:\n{src}"
                    );
                    refused_redundant += 1;
                }
                // Refused for another reason, the refusal must not depend on
                // the unreachable rows: Clean refuses the definition without
                // them too (a lowering it does not have yet, as for any valid
                // definition this battery may see refused).
                Err(error) => {
                    assert!(
                        env.get_const(&Name::from_string(&name)).is_none(),
                        "refused yet registered:\n{src}"
                    );
                    let reached = reachable_rows(&rows);
                    let pruned: Vec<Row> = rows
                        .iter()
                        .zip(&reached)
                        .filter(|(_, reached)| **reached)
                        .map(|(row, _)| row.clone())
                        .collect();
                    let pruned_name = format!("pruned{redundant_candidates}");
                    let pruned_src = rows_source(&pruned_name, &pruned, match_form);
                    assert!(
                        register(&mut env, &pruned_src).is_err(),
                        "refused for a reason other than its unreachable row, yet \
                         accepted without it:\n{src}\n{error}\n{pruned_src}"
                    );
                }
                Ok(()) => {
                    let tested = if match_form { 0 } else { 1 };
                    assert!(
                        !is_recursive(&rows) && structural_columns(&rows) <= tested,
                        "Lean refuses this (\"redundant alternative\") and it is not a \
                         ledger class (89) shape, so Clean must refuse it too:\n{src}"
                    );
                    class_89_first_match_values(&mut env, &name, &rows);
                }
            }
            redundant_candidates += 1;
        };
        let name = format!("r{def_id}");
        let src = rows_source(&name, &rows, match_form);
        if let Err(error) = register(&mut env, &src) {
            // A loud refusal; nothing may be registered under the name, and
            // every row of this definition is reachable.
            assert!(
                !error.contains("redundant alternative"),
                "every row is reachable, yet refused as redundant:\n{src}\n{error}"
            );
            assert!(env.get_const(&Name::from_string(&name)).is_none(), "{src}");
            continue;
        }
        for probe in 0..4 {
            let (x, y) = (rng.next(5), rng.next(5));
            let mut fuel = 10_000;
            let Some(truth) = eval(&rows, x, y, &mut fuel) else {
                continue;
            };
            let call = format!("{name} {x} {y}");
            let wrong = truth + 1 + rng.next(3);
            refused(&mut env, &format!("{name}_{probe}"), &call, wrong);
            refused_false += 1;
            let good = format!("correct_{name}_{probe}");
            register(
                &mut env,
                &format!("theorem {good} : {call} = {truth} := rfl"),
            )
            .unwrap_or_else(|error| panic!("{src}\n{call} = {truth} must hold: {error}"));
            accepted_true += 1;
        }
    }
    // Non-vacuity: most definitions lower, so the checks above have teeth.
    assert!(
        accepted_true >= 240 && refused_false >= 240,
        "battery too small to mean anything: {accepted_true} true / {refused_false} false"
    );
    assert!(
        refused_redundant > 0,
        "no candidate with an unreachable row was refused as redundant \
         ({redundant_candidates} generated); the reason checks above are vacuous"
    );
}

/// Whether some row calls the function.
fn is_recursive(rows: &[Row]) -> bool {
    rows.iter().any(|row| row.call.is_some())
}

/// Columns some row matches on (a literal or `v+1`; `_` and a variable match
/// everything).
fn structural_columns(rows: &[Row]) -> usize {
    (0..2)
        .filter(|&col| {
            rows.iter()
                .any(|row| matches!(row.pats[col], Pat::Lit(_) | Pat::Succ))
        })
        .count()
}

/// An ACCEPTED candidate (ledger class (89)): Lean refuses it, but the
/// lowering Clean gives it must still be first-match, so every input of the
/// exact domain `reachable_rows` uses is checked, TRUE and FALSE. It is not
/// recursive, so first-match evaluation always answers.
fn class_89_first_match_values(env: &mut Environment, name: &str, rows: &[Row]) {
    for x in 0..=3u64 {
        for y in 0..=3u64 {
            let mut fuel = 10_000;
            let truth = eval(rows, x, y, &mut fuel)
                .expect("a non-recursive definition ending in `_, _` always answers");
            computation(
                env,
                &format!("{name}_{x}_{y}"),
                &format!("{name} {x} {y}"),
                truth,
                truth + 1,
            );
        }
    }
}

#[test]
fn reconstructed_list_suffix_checks_every_adjacent_blob_digest() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        include_str!("recursion_scope_and_pattern_names/blobs_ascending.lean"),
    )
    .expect("original ordered-blob check must recurse on the immediate suffix");
    for wrong in [
        "theorem duplicates_pass : SemR.blobsAscending [([0],[]),([1],[7]),([1],[])] = true := rfl",
        "theorem distinct_refused : SemR.blobsAscending [([0],[5]),([1],[]),([2],[])] = false := rfl",
        "def reordered : List Nat → Bool | a :: b :: c :: rest => reordered (c :: b :: rest) | _ => true",
        "def unchanged : List Nat → Bool | a :: b :: rest => unchanged (a :: b :: rest) | _ => true",
    ] {
        assert!(register(&mut env, wrong).is_err(), "accepted {wrong}");
    }
}
