// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The order in which Lean's `decide` meets things, against pinned Lean
//! v4.30.0-rc2 (DECISIONS R127; third review of `fix/decide-lean-faithful`,
//! Q3–Q11): the `∀ b : Bool` instance matches `inst true` before
//! `inst false`; `synthInstance` tries every local instance in ONE pass, most
//! recent first, whatever its shape; it opens an alias goal (`DecidableEq α`)
//! before matching locals; it resolves a local's own `[inst]` binders as
//! sub-goals; and a `have` local stays a `have` whatever happens to the
//! hypotheses it mentions, while a sibling goal's `let` stays a `let`.
//!
//! Every verdict below was measured on
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean` (2026-10-23):
//!
//! ```text
//! axiom Q : Prop; axiom dQ : Decidable Q; noncomputable instance instQ := dQ
//!   (∀ b : Bool, b = true ∧ Q) → 3 = 4 := by decide        failed … stuck
//!   (∀ b : Bool, b = false ∧ Q) → 3 = 4 := by decide       accepted
//! the same with def R : Prop := True and an @[irreducible] stuckR instance
//! let i2 : Decidable (1 = 1) := isTrue (rfl : 1 = 1); have i1 : ∀ n,
//!   Decidable (n = 1) (or : DecidableEq Nat); decide       stuck at i1 1 (i1 1 1)
//! the same with the two lines swapped                       accepted
//! def f [i2 : Decidable (1 = 1)] [i1 : ∀ n, Decidable (n = 1)] := decide (1 = 1)
//!   elaborates to `i1 1`; with the binders swapped, `i2`; f1 [i1 : Decidable
//!   (1 = 2)] [i2 : DecidableEq Nat] := decide (1 = 2) elaborates to `i2 1 2`
//! (i : ∀ a b : Nat, Decidable (a = b)) ⊢ some 1 = some 1, [1] = [1]; the `have`
//!   form; [i : MyRel (fun a b => a = b)] (abbrev MyRel r := ∀ a b, Decidable
//!   (r a b)) ⊢ [1] = [1]                                   failed … stuck at i 1 1
//!   native_decide of the first             Cannot native decide … free variables
//!   (i : ∀ a b : Bool, …) ⊢ some 1 = some 1; (i : ∀ a b : Nat, Decidable (a < b))
//!   ⊢ [1] = [1]                                            accepted
//!   def h2 (i : …) : Bool := decide ([1] = [1]) elaborates to
//!   `instDecidableEqList Nat i …`
//! class Foo (n : Nat) : Prop; instance instFoo1 : Foo 1
//!   [inst : ∀ n, [Foo n] → Decidable (n = 1)] ⊢ 1 = 1; the `have` form
//!                                                          failed … stuck at inst 1
//!   def k [inst : …] := decide (1 = 1) elaborates to `inst 1 instFoo1`
//!   with class Bar and no Bar 1 instance                   accepted
//! def P : Prop := 1 = 1; have inst : Decidable (1 = 1) := isTrue h; then
//!   unfold P at h (or rw [P] at h, goal 1 = 1 ∧ True); decide
//!                                                          failed … stuck at inst
//!   the `let` twins                                        accepted
//! constructor; · have b : Bool := true; trivial · let b : Bool := true;
//!   have hb : b = true := by decide; trivial (and the Nat form) accepted
//! instance i2 : DecidableEq Nat := stuckDec (@[irreducible], default
//!   priority); 1 = 1 := by decide                          stuck at stuckDec
//! l : ∀ α [DecidableEq α], DecidableEq (W α) with a global `top` for W^6 B:
//!   decide (x = x) = decide (x = x) := rfl                  accepted (`top`)
//! l1 l2 : ∀ p [Decidable p], Decidable (S p) with a global `topI` for S^10 Q:
//!   the same `rfl`                                         accepted (`topI`)
//! KNOWN over-acceptances (pinned Lean REFUSES each; Clean accepts):
//!   instance myDec : Decidable (1 = 1) := myDecImpl (@[irreducible]);
//!     1 = 1 := by decide                                   stuck at myDecImpl
//!   noncomputable instance (priority := high) myEqDec : Decidable (1 = 1)
//!     := dE (axiom); 1 = 1 by decide / native_decide      stuck / noncomputable
//!   noncomputable instance (priority := high) myAll (a b) : Decidable (a =
//!     b) := dAll a b; 2 + 2 = 4, some 1 = some 1 := by decide   stuck at dAll
//!   class Foo (α) (β : outParam Type); g1 [i1 : Foo (Fin 3) Int] [i2 : ∀ n,
//!     Foo (Fin n) Bool] (x) := Foo.val x has type … → Int  Type mismatch (Bool)
//!   abbrev DP p := ∀ a, Decidable (p a); instQ [DP p] : Decidable (Q p);
//!     let j : DP …; have i : ∀ a b, Decidable (a = b); decide   stuck at i 1 1
//!   [inst : ∀ n m, [Foo m] → Decidable (n = 1)] ⊢ 1 = 1   stuck at inst 1 1
//!   have x : Nat := 5; have hx : x = 5 := by show 5 = 5; decide
//!                                                          'show' tactic failed
//!   have x : Nat := 5; have hx : x = 5 := by rfl            `rfl` failed
//! KNOWN refusals (pinned Lean ACCEPTS each; Clean refuses):
//!   instance (priority := 500) myInt : DecidableEq Int := stuckInt;
//!     some (1 : Int) = some 1 := by decide (and the Fin 5 form)   accepted
//! ```
//!
//! Each test was red at 8281dee6f, the head the third review named, except
//! the pins and the polynomial-search test (red at 3e0b5007c, whose local
//! `[inst]` search was exponential).

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};
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

/// A KNOWN over-acceptance: pinned Lean refuses `source` and Clean accepts it
/// (DECISIONS R127 "Not closed by this"). The day Clean refuses it too, this
/// fails, so the row moves to the refused ones with Lean's message.
#[track_caller]
fn expect_known_over_acceptance(source: &str) {
    if let Err(e) = elaborate_file(source) {
        panic!(
            "KNOWN GAP closed: Clean now refuses this, as pinned Lean does ({e}); \
             move the row to the refused ones and update R127\n{source}"
        );
    }
}

/// A KNOWN refusal: pinned Lean accepts `source` and Clean refuses it
/// (DECISIONS R127 "Not closed by this"); Clean's message. The day Clean
/// accepts it too, this fails, so the row moves to the accepted ones.
#[track_caller]
fn expect_known_refusal(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!(
            "KNOWN GAP closed: Clean now accepts this, as pinned Lean does; \
             move the row to the accepted ones and update R127\n{source}"
        ),
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

const STUCK: &str = "did not reduce to `isTrue` or `isFalse`";
const FREE_VARIABLES: &str = "Cannot native decide proposition with free variables";

/// The instance argument of the first `Decidable.decide` application in the
/// value of `name`, under its binders.
fn decided_instance(env: &Environment, name: &str) -> Expr {
    fn find(e: &Expr) -> Option<Expr> {
        let head = e.get_app_fn();
        let args = e.get_app_args();
        if let ExprKind::Const(n, _) = head.kind() {
            if (n == &Name::from_string("Decidable.decide") || n == &Name::from_string("decide"))
                && args.len() == 2
            {
                return Some(args[1].clone());
            }
        }
        match e.kind() {
            ExprKind::Lam(_, _, body) | ExprKind::Pi(_, _, body) => find(body),
            ExprKind::App(f, a) => find(f).or_else(|| find(a)),
            ExprKind::MData(_, inner) => find(inner),
            _ => None,
        }
    }
    let value = env
        .get_const(&Name::from_string(name))
        .and_then(|info| info.value.clone())
        .unwrap_or_else(|| panic!("{name} has a value"));
    find(&value).unwrap_or_else(|| panic!("{name}'s value applies `decide`: {value:?}"))
}

/// `true` iff `instance` is the bound variable `index` applied to `arity`
/// arguments.
fn is_bvar_applied(instance: &Expr, index: u32, arity: usize) -> bool {
    matches!(instance.get_app_fn().kind(), ExprKind::BVar(i) if *i as u64 == index as u64)
        && instance.get_app_args().len() == arity
}

/// `Bool.instDecidableForallOfDecidablePred` matches `inst true, inst false`:
/// the `true` case is reduced first, so a stuck `true` case is stuck even
/// when the `false` case is false (Q3).
#[test]
fn test_bool_forall_reduces_the_true_case_first() {
    let axiomatic = "axiom Q : Prop\naxiom dQ : Decidable Q\n\
        noncomputable instance instQ : Decidable Q := dQ\n";
    let irreducible = "def R : Prop := True\n\
        @[irreducible] def stuckR : Decidable R := Decidable.isTrue True.intro\n\
        instance instR : Decidable R := stuckR\n";
    for (decls, prop) in [(axiomatic, "Q"), (irreducible, "R")] {
        let source = format!(
            "{decls}theorem t : (∀ b : Bool, b = true ∧ {prop}) → (3 : Nat) = 4 := by decide\n"
        );
        assert_mentions(&expect_refused(&source), STUCK, &source);
        expect_accepted(&format!(
            "{decls}theorem t : (∀ b : Bool, b = false ∧ {prop}) → (3 : Nat) = 4 := by decide\n"
        ));
    }
}

/// Every local instance in one pass, most recent first, whatever its shape
/// (Q4, Q11).
#[test]
fn test_local_instances_in_one_pass_most_recent_first() {
    let older_let = "let i2 : Decidable ((1 : Nat) = 1) := Decidable.isTrue (rfl : (1 : Nat) = 1)";
    for newer_have in [
        "have i1 : ∀ n : Nat, Decidable (n = 1) := fun n => Nat.decEq n 1",
        "have i1 : DecidableEq Nat := fun a b => Nat.decEq a b",
    ] {
        let source =
            format!("theorem t : (1 : Nat) = 1 := by\n  {older_let}\n  {newer_have}\n  decide\n");
        assert_mentions(&expect_refused(&source), STUCK, &source);
        expect_accepted(&format!(
            "theorem t : (1 : Nat) = 1 := by\n  {newer_have}\n  {older_let}\n  decide\n"
        ));
    }

    let env = expect_accepted(
        "def f [i2 : Decidable ((1 : Nat) = 1)] [i1 : ∀ n : Nat, Decidable (n = 1)] : Bool := \
         decide ((1 : Nat) = 1)\n\
         def g [i1 : ∀ n : Nat, Decidable (n = 1)] [i2 : Decidable ((1 : Nat) = 1)] : Bool := \
         decide ((1 : Nat) = 1)\n\
         def f1 [i1 : Decidable ((1 : Nat) = 2)] [i2 : DecidableEq Nat] : Bool := \
         decide ((1 : Nat) = 2)\n",
    );
    // Lean: `i1 1`, `i2`, `i2 1 2` — the most recent binder, de Bruijn 0.
    for (name, arity) in [("f", 1), ("g", 0), ("f1", 2)] {
        let instance = decided_instance(&env, name);
        assert!(
            is_bvar_applied(&instance, 0, arity),
            "{name}: pinned Lean takes the most recent local instance (applied to {arity} \
             argument(s)); Clean took {instance:?}"
        );
    }
}

/// A `DecidableEq α` goal is opened to `∀ a b, Decidable (a = b)` before the
/// local instances are matched, so a local of that shape answers it (Q5).
#[test]
fn test_alias_goal_is_opened_for_local_instances() {
    let local = "(i : ∀ a b : Nat, Decidable (a = b))";
    for goal in ["some (1 : Nat) = some 1", "[(1 : Nat)] = [1]"] {
        let source = format!("theorem t {local} : {goal} := by decide\n");
        assert_mentions(&expect_refused(&source), STUCK, &source);
    }
    let source = "theorem t : some (1 : Nat) = some 1 := by\n  \
        have i : ∀ a b : Nat, Decidable (a = b) := fun a b => Nat.decEq a b\n  decide\n";
    assert_mentions(&expect_refused(source), STUCK, source);
    let source = "abbrev MyRel (r : Nat → Nat → Prop) := ∀ a b, Decidable (r a b)\n\
        theorem t [i : MyRel (fun a b : Nat => a = b)] : [(1 : Nat)] = [1] := by decide\n";
    assert_mentions(&expect_refused(source), STUCK, source);
    let source = format!("theorem t {local} : some (1 : Nat) = some 1 := by native_decide\n");
    assert_mentions(&expect_refused(&source), FREE_VARIABLES, &source);

    for (binders, goal) in [
        (
            "(i : ∀ a b : Bool, Decidable (a = b))",
            "some (1 : Nat) = some 1",
        ),
        ("(i : ∀ a b : Nat, Decidable (a < b))", "[(1 : Nat)] = [1]"),
    ] {
        expect_accepted(&format!("theorem t {binders} : {goal} := by decide\n"));
    }

    let env = expect_accepted(&format!(
        "def h2 {local} : Bool := decide ([(1 : Nat)] = [1])\n"
    ));
    let used = decided_instance(&env, "h2").collect_constants();
    assert!(
        !used.contains(&Name::from_string("instDecidableEqNat"))
            && !used.contains(&Name::from_string("Nat.decEq")),
        "pinned Lean elaborates `instDecidableEqList Nat i …`: the local answers the \
         `DecidableEq Nat` sub-goal; Clean used {used:?}"
    );
}

/// A local instance's own `[inst]` binders are sub-goals (Lean's
/// `synthOrder`): resolved, the local answers; unresolvable, the search moves
/// on (Q6).
#[test]
fn test_local_instance_with_instance_binders() {
    let foo = "class Foo (n : Nat) : Prop\ninstance instFoo1 : Foo 1 := ⟨⟩\n";
    let source = format!(
        "{foo}theorem t [inst : ∀ n, [Foo n] → Decidable (n = 1)] : (1 : Nat) = 1 := by decide\n"
    );
    assert_mentions(&expect_refused(&source), STUCK, &source);
    let source = format!(
        "{foo}theorem t : (1 : Nat) = 1 := by\n  \
         have inst : ∀ n, [Foo n] → Decidable (n = 1) := fun n _ => Nat.decEq n 1\n  decide\n"
    );
    assert_mentions(&expect_refused(&source), STUCK, &source);
    expect_accepted(
        "class Bar (n : Nat) : Prop\n\
         theorem t [inst : ∀ n, [Bar n] → Decidable (n = 1)] : (1 : Nat) = 1 := by decide\n",
    );
    let env = expect_accepted(&format!(
        "{foo}def k [inst : ∀ n, [Foo n] → Decidable (n = 1)] : Bool := decide ((1 : Nat) = 1)\n"
    ));
    let instance = decided_instance(&env, "k");
    assert!(
        is_bvar_applied(&instance, 0, 2)
            && instance
                .collect_constants()
                .contains(&Name::from_string("instFoo1")),
        "pinned Lean elaborates `inst 1 instFoo1`; Clean took {instance:?}"
    );
}

/// A `have` local stays a `have` after a hypothesis it mentions is rewritten
/// (Q7), and a sibling goal's `let` with the same value stays a `let` (Q8).
#[test]
fn test_have_is_a_property_of_the_declaration() {
    let p = "def P : Prop := (1 : Nat) = 1\n";
    for (goal, rewrite) in [
        ("(1 : Nat) = 1", "unfold P at h"),
        ("(1 : Nat) = 1 ∧ True", "rw [P] at h"),
    ] {
        let source = format!(
            "{p}theorem t (h : P) : {goal} := by\n  \
             have inst : Decidable ((1 : Nat) = 1) := Decidable.isTrue h\n  {rewrite}\n  decide\n"
        );
        assert_mentions(&expect_refused(&source), STUCK, &source);
        expect_accepted(&format!(
            "{p}theorem t (h : P) : {goal} := by\n  \
             let inst : Decidable ((1 : Nat) = 1) := Decidable.isTrue h\n  {rewrite}\n  decide\n"
        ));
    }
    for (ty, value) in [("Bool", "true"), ("Nat", "5")] {
        expect_accepted(&format!(
            "theorem t : True ∧ True := by\n  constructor\n  \
             · have b : {ty} := {value}\n    trivial\n  \
             · let b : {ty} := {value}\n    have hb : b = {value} := by decide\n    trivial\n"
        ));
    }
}

/// A local's `[inst]` sub-goals cost the search linear work: a sub-goal that
/// failed is not searched again in the same query, and the global instance
/// Lean picks is still found (pinned Lean accepts both, with `top` / `topI`).
/// Before, a `[DecidableEq α]` binder was searched three times per level and
/// two locals of one conclusion twice per level, the budget ran out, and
/// `top` was never tried.
#[test]
fn test_local_instance_sub_goals_stay_polynomial() {
    expect_accepted(
        "structure W (α : Type) where\n  val : α\n\
         axiom B : Type\n\
         axiom topAx : DecidableEq (W (W (W (W (W (W B))))))\n\
         noncomputable instance top : DecidableEq (W (W (W (W (W (W B)))))) := topAx\n\
         theorem t (l : ∀ (α : Type) [DecidableEq α], DecidableEq (W α))\n    \
         (x : W (W (W (W (W (W B)))))) : decide (x = x) = decide (x = x) := rfl\n",
    );
    let s10 = "S (S (S (S (S (S (S (S (S (S Q)))))))))";
    expect_accepted(&format!(
        "axiom Q : Prop\naxiom S : Prop → Prop\naxiom topS : Decidable ({s10})\n\
         noncomputable instance topI : Decidable ({s10}) := topS\n\
         theorem t (l1 l2 : ∀ p : Prop, [Decidable p] → Decidable (S p)) :\n    \
         decide ({s10}) = decide ({s10}) := rfl\n"
    ));
}

/// A newer user instance of default priority answers before the prelude's,
/// as in Lean (Lean by recency; Clean because the prelude's instance is
/// registered at a lower priority).
#[test]
fn test_a_newer_user_instance_answers_before_the_prelude() {
    let source = "@[irreducible] def stuckDec : DecidableEq Nat := fun a b => Nat.decEq a b\n\
        instance i2 : DecidableEq Nat := stuckDec\n\
        theorem t : (1 : Nat) = 1 := by decide\n";
    assert_mentions(&expect_refused(source), STUCK, source);
}

/// KNOWN over-acceptances, pinned (DECISIONS R127 "Not closed by this").
#[test]
fn test_known_over_acceptances() {
    // (l) The `Decidable (a = b)` → `DecidableEq α` bridge runs before the
    // global `Decidable` candidates, so a later or higher-priority user
    // instance loses to it, for `decide`, for `native_decide`, and for a
    // derived instance's parameter sub-goal.
    expect_known_over_acceptance(
        "@[irreducible] def myDecImpl : Decidable ((1 : Nat) = 1) := Decidable.isTrue rfl\n\
         instance myDec : Decidable ((1 : Nat) = 1) := myDecImpl\n\
         theorem t : (1 : Nat) = 1 := by decide\n",
    );
    let high = "axiom dE : Decidable ((1 : Nat) = 1)\n\
        noncomputable instance (priority := high) myEqDec : Decidable ((1 : Nat) = 1) := dE\n";
    for tactic in ["decide", "native_decide"] {
        expect_known_over_acceptance(&format!("{high}theorem t : (1 : Nat) = 1 := by {tactic}\n"));
    }
    let generic = "axiom dAll : ∀ a b : Nat, Decidable (a = b)\n\
        noncomputable instance (priority := high) myAll (a b : Nat) : Decidable (a = b) := \
        dAll a b\n";
    for goal in ["(2 : Nat) + 2 = 4", "some (1 : Nat) = some 1"] {
        expect_known_over_acceptance(&format!("{generic}theorem t : {goal} := by decide\n"));
    }
    // (h) A newer `∀`-typed local that matches only by assigning an
    // out-parameter is not taken; Lean assigns it (`preprocessOutParam`) and
    // elaborates `i2 3`, of type `Bool`.
    expect_known_over_acceptance(
        "class Foo (α : Type) (β : outParam Type) where\n  val : α → β\n\
         def g1 [i1 : Foo (Fin 3) Int] [i2 : ∀ n : Nat, Foo (Fin n) Bool] (x : Fin 3) := \
         Foo.val x\n\
         theorem t : (@g1 : [Foo (Fin 3) Int] → [∀ n : Nat, Foo (Fin n) Bool] → Fin 3 → Int) \
         = @g1 := rfl\n",
    );
    // (o) An alias goal that is not a registered class (`DP p`) is matched
    // against the locals before it is opened, so an older local of the whole
    // alias beats a newer one of its opened conclusion.
    expect_known_over_acceptance(
        "abbrev DP (p : Nat → Prop) := ∀ a, Decidable (p a)\n\
         def Q (p : Nat → Prop) : Prop := p 1\n\
         instance instQ (p : Nat → Prop) [h : DP p] : Decidable (Q p) := h 1\n\
         theorem t : Q (fun n => n = 1) := by\n  \
         let j : DP (fun n : Nat => n = 1) := fun n => Nat.decEq n 1\n  \
         have i : ∀ a b : Nat, Decidable (a = b) := fun a b => Nat.decEq a b\n  decide\n",
    );
    // (p) A local's `[inst]` sub-goal whose argument only the local's own
    // telescope determines (`Foo ?m`) is refused as open, so the local is
    // skipped; Lean assigns `?m` and is stuck at `inst 1 1`.
    expect_known_over_acceptance(
        "class Foo (n : Nat) : Prop\ninstance instFoo1 : Foo 1 := ⟨⟩\n\
         theorem t [inst : ∀ n m : Nat, [Foo m] → Decidable (n = 1)] : (1 : Nat) = 1 := \
         by decide\n",
    );
}

/// R127 (n), closed by the opaque-have reduction view (fc9f9dd5c): a tactic
/// `have` local has no value for `show` and `rfl` either, as in pinned Lean
/// (4.8.0, 4.30.0-rc2 and 4.36.0-rc2 refuse both: "`show` tactic failed,
/// pattern 5 = 5 is not definitionally equal to target x = 5" and "Tactic
/// `rfl` failed: The left-hand side x is not definitionally equal to the
/// right-hand side 5"). The `let` forms, which both pinned Leans accept, are
/// the controls.
#[test]
fn test_a_have_local_is_opaque_to_show_and_rfl() {
    for (proof, tactic) in [
        ("by\n    show 5 = 5\n    decide", "`show`"),
        ("by rfl", "`rfl`"),
    ] {
        let body = format!("  have hx : x = 5 := {proof}\n  trivial\n");
        let source = format!("theorem t : True := by\n  have x : Nat := 5\n{body}");
        assert_mentions(&expect_refused(&source), tactic, &source);
        expect_accepted(&format!(
            "theorem t : True := by\n  let x : Nat := 5\n{body}"
        ));
    }
}

/// KNOWN refusals where pinned Lean accepts (DECISIONS R127 (m)): the
/// prelude registers `instDecidableEqInt` and `Fin`'s instance at priority
/// 100 where Lean's are at 1000, so a priority-500 user instance answers the
/// equation stand-in's parameter sub-goal in Clean and loses in Lean.
#[test]
fn test_known_refusals_from_prelude_priorities() {
    for (decls, goal) in [
        (
            "@[irreducible] def stuckInt : DecidableEq Int := fun a b => Int.decEq a b\n\
             instance (priority := 500) myInt : DecidableEq Int := stuckInt\n",
            "some (1 : Int) = some 1",
        ),
        (
            "@[irreducible] def sFin : DecidableEq (Fin 5) := fun a b => decEq a b\n\
             instance (priority := 500) mFin : DecidableEq (Fin 5) := sFin\n",
            "some (3 : Fin 5) = some 3",
        ),
    ] {
        let source = format!("{decls}theorem t : {goal} := by decide\n");
        assert_mentions(&expect_known_refusal(&source), STUCK, &source);
    }
}
