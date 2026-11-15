// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `#reduce` (`crate::reduce_command`) against pinned Lean 4.30.0-rc2.
//!
//! Every Lean verdict cited below was measured on the pinned binary
//! (`~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean`,
//! 2026-11-13). Clean accepts a `#reduce` only when Lean's `Meta.reduce`
//! returns the term untouched (it is a type by `isTypeQuick`, and types are
//! skipped); everything else is refused by name. The negative controls are
//! each a `#reduce` pinned Lean rejects.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, CommandOutput,
    ElabError, ElabResult, FileContext,
};
use clean_kernel::{Environment, Expr, Name};

/// Each top-level command's outcome: its `#reduce` / `#eval` text, or the
/// error it failed with.
fn outcomes_in(mut env: Environment, src: &str) -> Vec<Result<Option<String>, ElabError>> {
    let decls = clean_parser::parse_file(src).unwrap_or_else(|e| panic!("must parse: {e:?}"));
    let mut file_ctx = FileContext::new();
    file_ctx.set_main_module(Name::from_string("ReduceTest"));
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
                .and_then(|result| output_of(&result))
        })
        .collect()
}

/// The `#reduce` / `#eval` text in `result`, looking inside a namespace or
/// section block; a member that failed inside a block is its error.
fn output_of(result: &ElabResult) -> Result<Option<String>, ElabError> {
    match result {
        ElabResult::Command(CommandOutput::Reduce(r)) => Ok(Some(r.value.clone())),
        ElabResult::Command(CommandOutput::Eval(r)) => Ok(Some(r.value.clone())),
        ElabResult::Failed { error, .. } => Err((**error).clone()),
        ElabResult::Multiple(results) => {
            let mut found = None;
            for inner in results {
                if let Some(value) = output_of(inner)? {
                    found = Some(value);
                }
            }
            Ok(found)
        }
        _ => Ok(None),
    }
}

/// The last command of `src`; every earlier one must elaborate.
fn last_outcome(src: &str) -> Result<Option<String>, ElabError> {
    let mut all = outcomes_in(Environment::with_prelude(), src);
    let last = all
        .pop()
        .unwrap_or_else(|| panic!("`{src}` has no command"));
    for (idx, earlier) in all.iter().enumerate() {
        assert!(
            earlier.is_ok(),
            "declaration {idx} of `{src}` must elaborate: {earlier:?}"
        );
    }
    last
}

fn reduced(src: &str) -> String {
    match last_outcome(src) {
        Ok(Some(value)) => value,
        other => panic!("`{src}` must be accepted, as pinned Lean accepts it; got {other:?}"),
    }
}

fn assert_refused(src: &str, needle: &str) {
    match last_outcome(src) {
        Err(ElabError::ReduceUnmodeled { reason }) => {
            assert!(
                reason.contains(needle),
                "`{src}`: refusal `{reason}` must name `{needle}`"
            );
        }
        other => panic!("`{src}` must be refused by name (`#reduce` refused), got {other:?}"),
    }
}

const NOT_A_TYPE: &str = "isTypeQuick";

#[test]
fn test_reduce_type_is_returned_unreduced_and_accepted() {
    // `elab/expandExplicitBinders.lean` verbatim: pinned Lean prints
    // `(a : Type u_1) × a`. The term is a type, which `Meta.reduce` skips,
    // so it is never reduced to `String` (and never `#eval`'d: it used to be
    // refused for want of a `Repr`).
    let file = "namespace MySigma\n  /-- We define a new `Sigma` -/\n  \
                def Sigma {α : Type u} (β : α → Type v)\n    := String\n\n  \
                #reduce Σ a, a\nend MySigma\n";
    let all = outcomes_in(Environment::with_prelude(), file);
    let reduce = all
        .iter()
        .find_map(|o| match o {
            Ok(Some(value)) => Some(value.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the `#reduce` must be accepted: {all:?}"));
    assert!(all.iter().all(Result::is_ok), "{all:?}");
    assert!(
        reduce.contains("Sigma") && !reduce.contains("String"),
        "`Σ` is the root `Sigma`, returned untouched: {reduce}"
    );
    assert_eq!(reduced("#reduce Nat"), "Nat");
    assert!(reduced("#reduce Type").contains("Type"));
    assert!(reduced("#reduce Nat → Nat").contains("Nat"));
    assert!(reduced("#reduce List Nat").contains("List"));
    // `(proofs := true)` does not change a skipped type.
    assert_eq!(reduced("#reduce (proofs := true) Nat"), "Nat");
}

#[test]
fn test_reduce_of_a_type_with_a_definition_is_a_named_gap() {
    // Known gaps, pinned as refusals: pinned Lean accepts both (printing
    // `MySig fun a => a` and `T 5000`), but a definition in the term is
    // refused (`reduce_command::definition_free`).
    let src = "def MySig {α : Type u} (β : α → Type v) : Type := String\n\
               #reduce MySig (fun (a : Type) => a)";
    assert_refused(src, "MySig");
    let src = "def T : Nat → Type\n  | 0 => Nat\n  | n + 1 => T n\n#reduce T 5000";
    assert_refused(src, "neither an inductive type");
}

#[test]
fn test_reduce_nat_pow_past_lean_threshold_is_refused() {
    // Negative controls (round-2 review, scratchpad `rv/p1..p4.lean`):
    // pinned Lean warns `exponent 300 exceeds the threshold 256` and fails
    // with `maximum recursion depth has been reached` on each. The kernel
    // folds `Nat.pow` in one step, so no kernel-normalization envelope may
    // decide these.
    for src in [
        "#reduce (2:Nat)^300",
        "#reduce (2:Nat)^300 % 7",
        "#reduce (2:Nat)^300 == 0",
        "#reduce Nat.pow 2 300 == 0",
    ] {
        assert_refused(src, NOT_A_TYPE);
    }
}

#[test]
fn test_reduce_native_string_folds_are_refused() {
    // Negative controls (`rv/s1.lean`, `rv/s3.lean`, `rv/s6.lean`): pinned
    // Lean fails each with `maximum recursion depth has been reached`;
    // Clean's kernel folds them through native `String` reducers.
    let long = "a".repeat(3000);
    let medium = "a".repeat(600);
    for src in [
        format!("#reduce \"{long}\".length"),
        format!("#reduce (\"{medium}\" ++ \"b\").length"),
    ] {
        assert_refused(&src, NOT_A_TYPE);
    }
    // The built-in prelude has no `String.utf8ByteSize`; whatever refuses it
    // here, it must not be accepted (the Lean-world CLI run refuses it by
    // name too, measured 2026-11-13).
    let src = format!("#reduce \"{long}\".utf8ByteSize");
    let outcome = last_outcome(&src);
    assert!(outcome.is_err(), "`{src}` must be refused, got {outcome:?}");
}

#[test]
fn test_reduce_deep_normal_form_is_refused() {
    // Negative controls: pinned Lean rejects both with `maximum recursion
    // depth has been reached`.
    let rep = "def rep : Nat → List Nat\n  | 0 => []\n  | n + 1 => n :: rep n\n";
    assert_refused(&format!("{rep}#reduce rep 3000"), NOT_A_TYPE);
    assert_refused(&format!("{rep}#reduce (rep 20000).length"), NOT_A_TYPE);
}

#[test]
fn test_reduce_of_a_value_is_a_named_gap() {
    // Known gaps, pinned as refusals: pinned Lean accepts each (printing
    // `5`, `fun x => x`, `fun n => …` and `[]`). Clean does not model
    // Lean's reduction, so it refuses rather than guess where Lean stops.
    for src in [
        "#reduce 2 + 3",
        "#reduce fun x : Nat => x",
        "#reduce fun n : Nat => 1 + n",
        "#reduce \"\".data",
    ] {
        assert_refused(src, NOT_A_TYPE);
    }
    // `(types := true)` makes Lean reduce types too (it accepts
    // `#reduce (types := true) Nat`); not modeled.
    assert_refused("#reduce (types := true) Nat", "types := true");
    assert_refused(
        "#reduce (proofs := true) (types := true) Nat",
        "types := true",
    );
}

#[test]
fn test_reduce_of_an_undeclared_universe_is_refused() {
    // Negative controls: pinned Lean fails `#reduce Sort u` and `#reduce
    // Type u` with `unknown universe level `u``. Clean's elaborator binds the
    // name (it accepts `#check Sort u` too), so the command refuses every
    // universe parameter. Known gap: Lean accepts `universe u` then
    // `#reduce Sort u`.
    assert_refused("#reduce Sort u", "universe parameter");
    assert_refused("#reduce Type u", "universe parameter");
    assert_refused("universe u\n#reduce Sort u", "universe parameter");
}

#[test]
fn test_reduce_of_a_type_whose_check_unfolds_a_definition_is_refused() {
    // Negative controls: pinned Lean fails each `#reduce` with `maximum
    // recursion depth has been reached`, the first unifying `Nat` with
    // `T 5000`, the second even though the types are written identically
    // (Lean's `isDefEq` unfolds `T 5000`; it also fails `example (n : T 5000)
    // : T 5000 := n`), the third in the `constructorNameAsVariable` linter.
    // Clean's kernel finds each cheap, so a definition anywhere in the
    // term's constants' types is refused.
    let family = "def T : Nat → Type\n  | 0 => Nat\n  | n + 1 => T n\naxiom f : T 5000 → Type\n";
    for tail in [
        "axiom n : Nat\n#reduce f n",
        "axiom n : T 5000\n#reduce f n",
        "#reduce (x : T 5000) → Nat",
    ] {
        assert_refused(&format!("{family}{tail}"), "neither an inductive type");
    }
    // Control: with no definition in sight the same shape is accepted
    // (pinned Lean prints `g m`).
    assert_eq!(
        reduced("axiom A : Type\naxiom g : A → Type\naxiom m : A\n#reduce g m"),
        "g m"
    );
}

#[test]
fn test_reduce_conversion_free_refuses_an_unreduced_argument_type() {
    // `conversion_free` is a second, independent net: an argument whose type
    // is only convertible to its domain is refused even with no definition
    // in sight. Pinned Lean accepts this one (`F ((fun x => x) A)` checks by
    // beta); the refusal is a known gap of the backstop.
    let src = "axiom A : Type\naxiom F : ((fun (x : Type) => x) A) → Type\naxiom a : A\n\
               #reduce F a";
    match last_outcome(src) {
        Err(ElabError::ReduceUnmodeled { .. }) => {}
        other => panic!("`{src}` must be refused by name, got {other:?}"),
    }
}

#[test]
fn test_reduce_under_a_changed_bound_is_refused() {
    // Negative control: pinned Lean rejects `set_option maxRecDepth 8 in
    // #reduce [1, …, 12]` (maximum recursion depth). A bound set in scope is
    // refused whatever the term.
    assert_refused("set_option maxRecDepth 8 in\n#reduce Nat", "maxRecDepth");
    assert_refused(
        "set_option maxHeartbeats 1 in\n#reduce Nat",
        "maxHeartbeats",
    );
}

#[test]
fn test_reduce_under_warning_as_error_is_refused() {
    // Negative controls: pinned Lean v4.30.0-rc2 rejects each of these
    // (the constructorNameAsVariable linter, a deprecation warning and an
    // unused-variable warning, each promoted to an error), and Clean models
    // none of those warnings, so `#reduce` under `warningAsError` is refused
    // whatever its value or term.
    assert_refused(
        "set_option warningAsError true\n#reduce (zero : Nat) → Nat",
        "warningAsError",
    );
    assert_refused(
        "set_option warningAsError true\n@[deprecated \"x\" (since := \"2020-01-01\")] inductive A : Type\n#reduce A",
        "warningAsError",
    );
    assert_refused(
        "set_option warningAsError true\n#reduce (fun (x : Type) => Nat) Nat",
        "warningAsError",
    );
    assert_refused(
        "set_option warningAsError true in\n#reduce (fun (x : Type) => Nat) Nat",
        "warningAsError",
    );
}

#[test]
fn test_reduce_output_is_never_judged_by_guard_msgs() {
    // Clean's rendering is not Lean's delaborator. Negative control: pinned
    // Lean rejects `/-- info: Bool -/ #guard_msgs in #reduce Nat` (the
    // message is `Nat`). Every `#guard_msgs` over a `#reduce` is refused,
    // whatever it expects and whatever it drops.
    for src in [
        "/-- info: Nat -/\n#guard_msgs in\n#reduce Nat",
        "/-- info: Bool -/\n#guard_msgs in\n#reduce Nat",
        "#guard_msgs (drop info) in\n#reduce Nat",
    ] {
        assert_refused(src, "#guard_msgs");
    }
    // A refusal is not a message a `drop` can launder.
    match last_outcome("#guard_msgs (drop all) in\n#reduce (2:Nat)^300") {
        Err(ElabError::ReduceUnmodeled { reason }) => assert!(
            reason.contains(NOT_A_TYPE),
            "the reduction's own refusal surfaces: {reason}"
        ),
        other => panic!("the refusal must surface, got {other:?}"),
    }
}

#[test]
fn test_reduce_never_runs_an_io_action() {
    // The built-in prelude has no `IO` since bcacce6e0; the explicit IO
    // fragment registers the action under the name the IO runtime
    // (`crate::io_bridge`) executes.
    let env = || {
        let mut env = Environment::with_prelude();
        assert!(
            env.get_const(&Name::from_string("IO.FS.writeFile"))
                .is_none(),
            "the default prelude must not carry the IO fragment"
        );
        env.init_io_stub_theory()
            .expect("the explicit IO fragment must kernel-check");
        assert!(
            env.get_const(&Name::from_string("IO.FS.writeFile"))
                .is_some(),
            "the IO fragment registers the action"
        );
        env
    };
    let dir = tempfile::tempdir().expect("temp dir");
    let by_eval = dir.path().join("by_eval.txt");
    let by_reduce = dir.path().join("by_reduce.txt");
    // Control: `#eval` of the action writes the file, so the check below is
    // not vacuous.
    let eval = outcomes_in(
        env(),
        &format!("#eval IO.FS.writeFile \"{}\" \"x\"", by_eval.display()),
    );
    assert!(eval.iter().all(Result::is_ok), "control `#eval`: {eval:?}");
    assert!(by_eval.exists(), "control `#eval` must write the file");
    let reduce = outcomes_in(
        env(),
        &format!("#reduce IO.FS.writeFile \"{}\" \"x\"", by_reduce.display()),
    );
    assert!(
        matches!(reduce.last(), Some(Err(ElabError::ReduceUnmodeled { .. }))),
        "an `IO` action is no type: refused by name, {reduce:?}"
    );
    assert!(!by_reduce.exists(), "`#reduce` must not run its term");
}

#[test]
fn test_whnf_and_norm_num_are_not_commands() {
    // Negative controls: pinned Lean without Mathlib rejects both
    // (`unexpected token '#'; expected command`). Both used to be `#eval`.
    for src in ["#whnf 1", "#norm_num 1 + 1"] {
        let outcome = last_outcome(src);
        assert!(outcome.is_err(), "`{src}` must be refused, got {outcome:?}");
    }
}

#[test]
fn test_is_type_quick_transcribes_lean() {
    use crate::reduce_command::{is_type_quick, LBool};
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let list = Expr::const_(Name::from_string("List"), vec![clean_kernel::Level::zero()]);
    assert_eq!(
        is_type_quick(&env, &Expr::sort(clean_kernel::Level::zero())),
        LBool::True
    );
    assert_eq!(is_type_quick(&env, &nat), LBool::True);
    assert_eq!(
        is_type_quick(&env, &Expr::app(list.clone(), nat.clone())),
        LBool::True
    );
    // `List` alone has type `Type u → Type u`: a function, not a type.
    assert_eq!(is_type_quick(&env, &list), LBool::False);
    assert_eq!(is_type_quick(&env, &Expr::nat_lit(3)), LBool::False);
    assert_eq!(
        is_type_quick(&env, &Expr::const_(Name::from_string("Nat.zero"), vec![])),
        LBool::Undef
    );
}
