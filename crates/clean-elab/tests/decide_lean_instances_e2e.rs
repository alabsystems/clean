// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which `Decidable` instance the registered `decide` / `native_decide`
//! (DECISIONS R127) reduce, against pinned Lean v4.30.0-rc2: Lean's
//! `synthInstance` tries the local instances before any global one at every
//! sub-goal (a `∀`-typed local and a `DecidableEq` local included), matches at
//! instance transparency (a semireducible `def` stays folded), synthesizes the
//! `∀ b : Bool` instance's `DecidablePred` with `b` free, and gives a `have`
//! local no value. The second review of `fix/decide-lean-faithful` (R1–R12)
//! found Clean wider than Lean on each.
//!
//! Every verdict below was measured on
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean` (2026-10-22):
//!
//! ```text
//! axiom P : Bool → Prop; instances for `P true` and `P false` only
//!   ∀ b : Bool, P b / False → ∀ b, P b / 1 = 2 → ∀ b, P b /
//!   ∀ b c : Bool, b = c → P b := by decide; ∀ b, P b := by native_decide
//!   ∀ b : Bool, (match b with | true => 1 = 1 | false => 2 = 2)
//!     (decide, native_decide)                          failed to synthesize
//!   P true ∧ P false := by decide                      accepted
//! noncomputable instance instG (b) : Decidable (Q b) := genericDec b (an
//!   axiom), then reducing instances for `Q true` / `Q false`
//!   ∀ b : Bool, Q b := by decide        failed … stuck (instG was used)
//!   Q true, Q true ∧ Q false := by decide              accepted
//! [Decidable (1 = 2)] ⊢ ¬ (1 = 2); [Decidable (1 = 1)] ⊢ 1 = 1 ∧ True,
//!   True ∧ 1 = 1, 1 = 1 ∨ False, 1 = 1 ∧ 2 = 2; [DecidableEq Nat] ⊢ ¬ (1 = 2),
//!   1 ≠ 2, [1] = [1], some 1 = some 1, (1, 2) = (1, 2);
//!   [∀ n : Nat, Decidable (n = 1)] / (inst : ∀ n, Decidable (n = 1)) ⊢ 1 = 1;
//!   [∀ a b : Nat, Decidable (a < b)] ⊢ 1 < 2;
//!   (inst : ∀ n, Decidable (n = n)) ⊢ 1 = 1          failed … stuck at inst
//! native_decide on [DecidableEq Nat] ⊢ ¬ (1 = 2), some 1 = some 1;
//!   (inst : ∀ n, Decidable (n = 1)) ⊢ 1 = 1; [∀ a b, Decidable (a < b)] ⊢
//!   1 < 2; [Decidable (1 = 2)] ⊢ ¬ (1 = 2)
//!     Cannot native decide proposition with free variables
//! [∀ n, Decidable (n = 1)] ⊢ 2 = 2 (decide, native_decide);
//!   [∀ a b, Decidable (a < b)] ⊢ 1 = 1; [Decidable (2 = 2)] ⊢ 1 = 1;
//!   [DecidableEq Bool] ⊢ ¬ (1 = 2), some 1 = some 1;
//!   [Decidable (3 = 3)] ⊢ ¬ (1 = 2); (inst : ∀ n, Decidable (n = 1)) ⊢
//!   ¬ (1 = 2)                                          accepted
//! have inst : Decidable (1 = 1) := isTrue rfl; decide   (also DecidableEq Nat,
//!   Decidable True, and Decidable (1 = 2) under ¬ (1 = 2))  failed … stuck
//! the same with `let`                                  accepted
//! def Pd n : Prop := n = 1: Pd 1 (decide, native_decide), 1 = 2 → Pd 1;
//!   def Bd b : Prop := b = b: ∀ b : Bool, Bd b; def Qd : Prop := 1 = 1: Qd;
//!   def Pm : Bool → Prop by match: Pm true, ∀ b, Pm b   failed to synthesize
//! abbrev Ra n : Prop := n = 1: Ra 1, 1 = 2 → Ra 1; abbrev BRa: ∀ b, BRa b
//!                                                      accepted
//! def f1 : Bool := decide (Pd 1)                       failed to synthesize
//! def f2 [inst : Decidable (1 = 2)] : Bool := decide (1 = 2)        `inst`
//! def f3 [inst : Decidable (1 = 2)] … decide (¬ 1 = 2)  `instDecidableNot inst`
//! def f4 [inst : DecidableEq Nat] … decide (1 = 2)      `inst 1 2`
//! def f5 (inst : ∀ n, Decidable (n = 2)) … decide (1 = 2)  `inst 1`
//! (∀ b : Bool, b = true) → 1 = 1; (1 = 2 → 3 = 4) → 5 = 5;
//!   (1 = 1 → 3 = 4) → 5 = 6; (some 1, true) = (some 1, true);
//!   ∀ b : Bool, some b = some b; some 1 = some 2 → False; ¬ (some 1 = some 2);
//!   axiom c : Nat ⊢ (⟨0, Nat.zero_lt_succ c⟩ : Fin (c+1)).val = 0
//!     := by native_decide                              accepted
//! have inst : Decidable (1 = 1) := Decidable.isTrue (rfl : 1 = 1); decide
//!   failed … stuck; the `let` twin, and the `let` twin with `rfl` unascribed
//!                                                      accepted
//! ```
//!
//! Each test was red at d26cdb181, the head the second review named.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_parser::parse_file;

fn inner_failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(inner_failure),
        _ => None,
    }
}

/// Elaborate every declaration of `source` against a fresh prelude; the
/// environment on success, the first error's message otherwise.
fn elaborate_file(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())?;
        if let Some(failure) = inner_failure(&result) {
            return Err(failure);
        }
    }
    Ok(env)
}

#[track_caller]
fn expect_accepted(source: &str) -> Environment {
    match elaborate_file(source) {
        Ok(env) => env,
        Err(e) => panic!("pinned Lean accepts this; Clean refused it: {e}\n{source}"),
    }
}

#[track_caller]
fn expect_refused(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("pinned Lean refuses this; Clean accepted it:\n{source}"),
        Err(message) => message,
    }
}

#[track_caller]
fn assert_mentions(message: &str, needle: &str, source: &str) {
    assert!(
        message.contains(needle),
        "expected `{needle}` for\n{source}\ngot: {message}"
    );
}

const NO_INSTANCE: &str = "failed to synthesize\n  Decidable";
const STUCK: &str = "did not reduce to `isTrue` or `isFalse`";
const FREE_VARIABLES: &str = "Cannot native decide proposition with free variables";

const PER_CASE: &str = "axiom P : Bool → Prop\naxiom hP : ∀ b, P b\n\
    instance instPt : Decidable (P true) := Decidable.isTrue (hP true)\n\
    instance instPf : Decidable (P false) := Decidable.isTrue (hP false)\n";

/// `Bool.instDecidableForallOfDecidablePred` needs `DecidablePred p`, which
/// Lean searches with `b` free: instances for `P true` and `P false` alone do
/// not give it (R1, R11).
#[test]
fn test_bool_forall_needs_one_instance_for_the_open_predicate() {
    let by_match = "∀ b : Bool, (match b with | true => (1 : Nat) = 1 | false => (2 : Nat) = 2)";
    for (goal, tactic) in [
        ("∀ b : Bool, P b", "decide"),
        ("False → ∀ b : Bool, P b", "decide"),
        ("1 = 2 → ∀ b : Bool, P b", "decide"),
        ("∀ b c : Bool, b = c → P b", "decide"),
        ("∀ b : Bool, P b", "native_decide"),
        (by_match, "decide"),
        (by_match, "native_decide"),
    ] {
        let source = format!("{PER_CASE}theorem t : {goal} := by {tactic}\n");
        assert_mentions(&expect_refused(&source), NO_INSTANCE, &source);
    }
    for goal in [
        "P true ∧ P false",
        "∀ b : Bool, b = b",
        "∀ a b : Bool, a = true → b = true → (a && b) = true",
    ] {
        expect_accepted(&format!("{PER_CASE}theorem t : {goal} := by decide\n"));
    }
}

/// The open predicate's instance is the one every case reduces: a generic
/// instance found with `b` free beats a more specific instance for one case,
/// though the specific one answers `Q true` asked alone (pinned Lean is stuck
/// at `genericDec true`).
#[test]
fn test_bool_forall_reduces_the_open_predicate_instance() {
    let decls = "axiom Q : Bool → Prop\naxiom hQ : ∀ b, Q b\n\
        axiom genericDec : ∀ b, Decidable (Q b)\n\
        noncomputable instance instG (b : Bool) : Decidable (Q b) := genericDec b\n\
        instance instQt : Decidable (Q true) := Decidable.isTrue (hQ true)\n\
        instance instQf : Decidable (Q false) := Decidable.isTrue (hQ false)\n";
    let source = format!("{decls}theorem t : ∀ b : Bool, Q b := by decide\n");
    assert_mentions(&expect_refused(&source), "stuck", &source);
    for goal in ["Q true", "Q true ∧ Q false"] {
        expect_accepted(&format!("{decls}theorem t : {goal} := by decide\n"));
    }
    expect_accepted(
        "abbrev BR (b : Bool) : Prop := b = b\ntheorem t : ∀ b : Bool, BR b := by decide\n",
    );
}

/// A false hypothesis accepts an implication without its conclusion being
/// reduced, at any depth: a false `∀ b : Bool` or a false implication is
/// false as a hypothesis too (pinned Lean accepts each).
#[test]
fn test_false_hypotheses_at_any_depth() {
    for goal in [
        "(∀ b : Bool, b = true) → (1 : Nat) = 1",
        "((1 : Nat) = 2 → (3 : Nat) = 4) → (5 : Nat) = 5",
        "((1 : Nat) = 1 → (3 : Nat) = 4) → (5 : Nat) = 6",
        "(some (1 : Nat), true) = (some 1, true)",
        "∀ b : Bool, some b = some b",
    ] {
        expect_accepted(&format!("theorem t : {goal} := by decide\n"));
    }
}

/// KNOWN GAPS, each pinned as a refusal so it fails loudly the day it closes
/// (DECISIONS R127 "Not closed by this"); pinned Lean ACCEPTS every row. When
/// one starts passing, move it to an accepted list.
#[test]
fn test_known_gaps_refuse_where_lean_accepts() {
    // A false equation over a type Clean has no `DecidableEq` instance of has
    // no refutation term, so it cannot discharge an implication.
    let source = "theorem t : some (1 : Nat) = some 2 → False := by decide\n";
    assert_mentions(&expect_refused(source), "no refutation term", source);
    // `instDecidableNot` needs that instance itself.
    let source = "theorem t : ¬ (some (1 : Nat) = some 2) := by decide\n";
    assert_mentions(&expect_refused(source), NO_INSTANCE, source);
    // The code walk does not tell a proof or type position from code: `c`
    // appears only in the `Fin` bound and its proof.
    let source = "axiom c : Nat\n\
        theorem t : (⟨0, Nat.zero_lt_succ c⟩ : Fin (c + 1)).val = 0 := by native_decide\n";
    assert_mentions(
        &expect_refused(source),
        "not supported by code generator",
        source,
    );
    // Clean's `let` tactic elaborates its value without the expected type, so
    // an unascribed `rfl` leaves elaborator metavariables the proof state
    // does not know (not `decide`'s; the ascribed twin above is accepted).
    let source = "theorem t : (1 : Nat) = 1 := by\n  \
        let inst : Decidable ((1 : Nat) = 1) := Decidable.isTrue rfl\n  decide\n";
    assert_mentions(&expect_refused(source), "Unknown free variable", source);
}

/// Local instances come first at every sub-goal, `∀`-typed and `DecidableEq`
/// locals included, so the reduction is stuck at the local (R2, R6, R7, R10).
#[test]
fn test_local_instances_answer_every_subgoal() {
    for (binders, goal) in [
        ("[Decidable ((1 : Nat) = 2)]", "¬ ((1 : Nat) = 2)"),
        ("[Decidable ((1 : Nat) = 1)]", "(1 : Nat) = 1 ∧ True"),
        ("[Decidable ((1 : Nat) = 1)]", "True ∧ (1 : Nat) = 1"),
        ("[Decidable ((1 : Nat) = 1)]", "(1 : Nat) = 1 ∨ False"),
        (
            "[Decidable ((1 : Nat) = 1)]",
            "(1 : Nat) = 1 ∧ (2 : Nat) = 2",
        ),
        ("[DecidableEq Nat]", "¬ ((1 : Nat) = 2)"),
        ("[DecidableEq Nat]", "(1 : Nat) ≠ 2"),
        ("[DecidableEq Nat]", "[(1 : Nat)] = [1]"),
        ("[DecidableEq Nat]", "some (1 : Nat) = some 1"),
        ("[DecidableEq Nat]", "((1 : Nat), (2 : Nat)) = (1, 2)"),
        ("[∀ n : Nat, Decidable (n = 1)]", "(1 : Nat) = 1"),
        ("(inst : ∀ n : Nat, Decidable (n = 1))", "(1 : Nat) = 1"),
        ("(inst : ∀ n : Nat, Decidable (n = n))", "(1 : Nat) = 1"),
        ("[∀ a b : Nat, Decidable (a < b)]", "(1 : Nat) < 2"),
    ] {
        let source = format!("theorem t {binders} : {goal} := by decide\n");
        assert_mentions(&expect_refused(&source), STUCK, &source);
    }
    for (binders, goal, tactic) in [
        ("[∀ n : Nat, Decidable (n = 1)]", "(2 : Nat) = 2", "decide"),
        (
            "[∀ n : Nat, Decidable (n = 1)]",
            "(2 : Nat) = 2",
            "native_decide",
        ),
        (
            "[∀ a b : Nat, Decidable (a < b)]",
            "(1 : Nat) = 1",
            "decide",
        ),
        ("[Decidable ((2 : Nat) = 2)]", "(1 : Nat) = 1", "decide"),
        ("[DecidableEq Bool]", "¬ ((1 : Nat) = 2)", "decide"),
        ("[DecidableEq Bool]", "some (1 : Nat) = some 1", "decide"),
        ("[Decidable ((3 : Nat) = 3)]", "¬ ((1 : Nat) = 2)", "decide"),
        (
            "(inst : ∀ n : Nat, Decidable (n = 1))",
            "¬ ((1 : Nat) = 2)",
            "decide",
        ),
    ] {
        expect_accepted(&format!("theorem t {binders} : {goal} := by {tactic}\n"));
    }
}

/// `native_decide` refuses `decide p` when its instance mentions a local, at
/// whatever depth the local instance was used.
#[test]
fn test_native_decide_refuses_local_instances_at_every_depth() {
    for (binders, goal) in [
        ("[DecidableEq Nat]", "¬ ((1 : Nat) = 2)"),
        ("[DecidableEq Nat]", "some (1 : Nat) = some 1"),
        ("(inst : ∀ n : Nat, Decidable (n = 1))", "(1 : Nat) = 1"),
        ("[∀ a b : Nat, Decidable (a < b)]", "(1 : Nat) < 2"),
        ("[Decidable ((1 : Nat) = 2)]", "¬ ((1 : Nat) = 2)"),
    ] {
        let source = format!("theorem t {binders} : {goal} := by native_decide\n");
        assert_mentions(&expect_refused(&source), FREE_VARIABLES, &source);
    }
}

/// A `have` local has no value in Lean, so a `Decidable` instance it binds is
/// stuck where the `let` twin reduces (R3, R5).
#[test]
fn test_have_bound_instance_stays_opaque() {
    for (goal, binding) in [
        // `rfl` ascribed: Clean's `let` tactic elaborates its value without
        // the expected type (a known gap, pinned below).
        (
            "(1 : Nat) = 1",
            "inst : Decidable ((1 : Nat) = 1) := Decidable.isTrue (rfl : (1 : Nat) = 1)",
        ),
        (
            "(1 : Nat) = 1",
            "inst : DecidableEq Nat := fun a b => Nat.decEq a b",
        ),
        (
            "True",
            "inst : Decidable True := Decidable.isTrue True.intro",
        ),
        (
            "¬ ((1 : Nat) = 2)",
            "inst : Decidable ((1 : Nat) = 2) := Nat.decEq 1 2",
        ),
    ] {
        let source = format!("theorem t : {goal} := by\n  have {binding}\n  decide\n");
        assert_mentions(&expect_refused(&source), STUCK, &source);
        expect_accepted(&format!(
            "theorem t : {goal} := by\n  let {binding}\n  decide\n"
        ));
    }
}

/// Instance search matches at instance transparency: a semireducible
/// Prop-valued `def` stays folded and has no instance; an `abbrev` unfolds
/// (R9, R12).
#[test]
fn test_semireducible_props_have_no_instance() {
    let decls = "def Pd (n : Nat) : Prop := n = 1\n\
        def Bd (b : Bool) : Prop := b = b\n\
        def Qd : Prop := (1 : Nat) = 1\n\
        def Pm : Bool → Prop\n  | true => (1 : Nat) = 1\n  | false => (2 : Nat) = 2\n";
    for (goal, tactic) in [
        ("Pd 1", "decide"),
        ("Pd 1", "native_decide"),
        ("1 = 2 → Pd 1", "decide"),
        ("∀ b : Bool, Bd b", "decide"),
        ("Qd", "decide"),
        ("Pm true", "decide"),
        ("∀ b : Bool, Pm b", "decide"),
    ] {
        let source = format!("{decls}theorem t : {goal} := by {tactic}\n");
        assert_mentions(&expect_refused(&source), NO_INSTANCE, &source);
    }
    let abbrevs = "abbrev Ra (n : Nat) : Prop := n = 1\nabbrev BRa (b : Bool) : Prop := b = b\n";
    for goal in ["Ra 1", "1 = 2 → Ra 1", "∀ b : Bool, BRa b"] {
        expect_accepted(&format!("{abbrevs}theorem t : {goal} := by decide\n"));
    }
}

/// The resolver serves the elaborator too: the same rules decide which
/// instance a term's `decide` slot gets.
#[test]
fn test_resolver_prefers_local_instances_and_instance_transparency() {
    let source = "def Pd (n : Nat) : Prop := n = 1\ndef f : Bool := decide (Pd 1)\n";
    assert_mentions(&expect_refused(source), "synthesize", source);
    expect_accepted("abbrev Ra (n : Nat) : Prop := n = 1\ndef f : Bool := decide (Ra 1)\n");

    for (binders, prop, wanted) in [
        ("[inst : Decidable ((1 : Nat) = 2)]", "(1 : Nat) = 2", None),
        (
            "[inst : Decidable ((1 : Nat) = 2)]",
            "¬ (1 : Nat) = 2",
            Some("instDecidableNot"),
        ),
        ("[inst : DecidableEq Nat]", "(1 : Nat) = 2", None),
        (
            "(inst : ∀ n : Nat, Decidable (n = 2))",
            "(1 : Nat) = 2",
            None,
        ),
    ] {
        let source = format!("def f {binders} : Bool := decide ({prop})\n");
        let env = expect_accepted(&source);
        let value = env
            .get_const(&Name::from_string("f"))
            .and_then(|info| info.value.clone())
            .expect("f has a value");
        let used = value.collect_constants();
        for global in ["instDecidableEqNat", "Nat.decEq"] {
            assert!(
                !used.contains(&Name::from_string(global)),
                "pinned Lean uses the local instance, not `{global}`, for\n{source}\ngot: {value:?}"
            );
        }
        assert!(
            wanted.is_none_or(|wanted| used.contains(&Name::from_string(wanted))),
            "expected `{wanted:?}` around the local instance for\n{source}\ngot: {value:?}"
        );
    }
}
