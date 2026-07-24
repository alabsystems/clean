// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic documentation entries, organized by category.
//!
//! Each per-category function returns a `Vec<TacticDoc>` for that category.
//! The top-level [`all_tactic_docs`] collects all categories.

use super::{TacticCategory, TacticDoc};

/// Helper to construct a `TacticDoc` concisely.
fn doc(
    name: &str,
    cat: TacticCategory,
    sig: &str,
    desc: &str,
    examples: &[&str],
    see_also: &[&str],
) -> TacticDoc {
    TacticDoc {
        name: name.to_string(),
        category: cat,
        signature: sig.to_string(),
        description: desc.to_string(),
        examples: examples.iter().map(|s| (*s).to_string()).collect(),
        see_also: see_also.iter().map(|s| (*s).to_string()).collect(),
    }
}

/// Collect documentation for all implemented tactics.
pub(super) fn all_tactic_docs() -> Vec<TacticDoc> {
    let mut docs = Vec::with_capacity(48);
    docs.extend(basic_docs());
    docs.extend(rewriting_docs());
    docs.extend(logic_docs());
    docs.extend(arithmetic_docs());
    docs.extend(search_docs());
    docs.extend(combinator_docs());
    docs.extend(closing_docs());
    docs.extend(advanced_docs());
    docs
}

fn basic_docs() -> Vec<TacticDoc> {
    use TacticCategory::Basic;
    vec![
        doc("intro", Basic, "intro (name : Name)",
            "Introduce a binder from the goal into the local context. \
             For a goal `forall (x : A), B x`, introduces `x : A` and changes the goal to `B x`.",
            &["intro h", "intro x y z"], &["intros", "apply"]),
        doc("intros", Basic, "intros (names : Name*)",
            "Introduce all leading binders from the goal. Equivalent to \
             repeatedly calling `intro` until the goal is no longer a forall/Pi type.",
            &["intros", "intros a b c"], &["intro"]),
        doc("exact", Basic, "exact (e : term)",
            "Close the current goal by providing an exact proof term `e` whose type matches the goal type.",
            &["exact h", "exact Nat.zero_lt_succ n"], &["apply", "assumption"]),
        doc("apply", Basic, "apply (e : term)",
            "Apply a function or lemma `e` to the current goal. If `e : A -> B` and the goal is `B`, \
             the goal changes to `A`. Creates subgoals for any remaining arguments.",
            &["apply Nat.succ_lt_succ", "apply And.intro"], &["exact", "constructor"]),
        doc("assumption", Basic, "assumption",
            "Close the goal using a hypothesis from the local context whose \
             type is definitionally equal to the goal type.",
            &["assumption"], &["exact", "trivial"]),
        doc("constructor", Basic, "constructor",
            "Apply the first applicable constructor of an inductive type. \
             For structures, this introduces the constructor and creates subgoals for each field.",
            &["constructor"], &["apply", "left", "right", "split"]),
    ]
}

fn rewriting_docs() -> Vec<TacticDoc> {
    use TacticCategory::Rewriting;
    vec![
        doc("rw", Rewriting, "rw [rules : term*]",
            "Rewrite the goal using the given rewrite rules (equalities). \
             Each rule `h : a = b` replaces occurrences of `a` with `b`. \
             Prefix with `<-` for right-to-left rewriting.",
            &["rw [h]", "rw [<- h1, h2]"], &["simp", "unfold", "conv"]),
        doc("simp", Rewriting, "simp [lemmas : term*] (config : SimpConfig?)",
            "Simplify the goal (and optionally hypotheses) using the simp lemma set. \
             Applies rewrite rules repeatedly until no more apply. \
             The default lemma set includes `@[simp]`-tagged lemmas.",
            &["simp", "simp [h]", "simp only [Nat.add_zero]"], &["simp_all", "dsimp", "norm_num"]),
        doc("simp_all", Rewriting, "simp_all [lemmas : term*]",
            "Simplify the goal and all hypotheses using the simp lemma set. \
             More aggressive than `simp` since it also rewrites hypotheses.",
            &["simp_all", "simp_all [h]"], &["simp", "dsimp"]),
        doc("unfold", Rewriting, "unfold (names : Name*)",
            "Unfold the definitions of the named constants in the goal. \
             Replaces a defined constant with its definition body.",
            &["unfold List.length", "unfold myDef"], &["delta", "simp", "dsimp"]),
        doc("dsimp", Rewriting, "dsimp [lemmas : term*]",
            "Definitional simplification: simplify the goal using only \
             definitional equalities (no propositional lemmas). Faster than `simp` but less powerful.",
            &["dsimp", "dsimp only [List.map]"], &["simp", "unfold", "norm_num"]),
        doc("simpa", Rewriting, "simpa [lemmas : term*]",
            "Simplify the goal then close it using `assumption`. \
             Equivalent to `simp [...]; assumption` but more concise.",
            &["simpa", "simpa [h1, h2]"], &["simp", "assumption"]),
    ]
}

fn logic_docs() -> Vec<TacticDoc> {
    use TacticCategory::Logic;
    vec![
        doc("cases", Logic, "cases (e : term)",
            "Perform case analysis on a term of an inductive type. Creates \
             one subgoal per constructor, with the discriminee replaced by the constructor pattern.",
            &["cases h", "cases n with | zero => ... | succ n => ..."],
            &["rcases", "induction", "by_cases"]),
        doc("rcases", Logic, "rcases (e : term) with pattern",
            "Recursive case analysis with pattern matching. More flexible than `cases`: \
             can destructure nested structures in one step.",
            &["rcases h with \\<ha, hb\\>", "rcases h with (rfl | h')"], &["cases", "obtain"]),
        doc("contradiction", Logic, "contradiction",
            "Close the goal by finding contradictory hypotheses in the context. \
             Looks for `h : False`, pairs `h : P` and `h' : Not P`, and other patterns.",
            &["contradiction"], &["exfalso", "absurd", "by_contra"]),
        doc("by_contra", Logic, "by_contra (h : Name?)",
            "Prove the goal by contradiction. Introduces the negation of the goal \
             as a hypothesis and changes the goal to `False`.",
            &["by_contra h", "by_contra"], &["contradiction", "exfalso"]),
        doc("split", Logic, "split",
            "Split a conjunction (`And`) goal into two subgoals, one for each conjunct.",
            &["split"], &["constructor", "left", "right", "And.intro"]),
        doc("left", Logic, "left",
            "Prove a disjunction by proving the left alternative. Changes the goal from `A Or B` to `A`.",
            &["left"], &["right", "split", "Or.inl"]),
        doc("right", Logic, "right",
            "Prove a disjunction by proving the right alternative. Changes the goal from `A Or B` to `B`.",
            &["right"], &["left", "split", "Or.inr"]),
        doc("exfalso", Logic, "exfalso",
            "Change the goal to `False`. Useful when you plan to derive a contradiction.",
            &["exfalso"], &["contradiction", "absurd", "by_contra"]),
        doc("by_cases", Logic, "by_cases (h : Prop)",
            "Split the proof into two cases: one where `h` holds and one where `Not h` holds.",
            &["by_cases h : n = 0"], &["cases", "split", "classical"]),
        doc("obtain", Logic, "obtain \\<a, b\\> := e",
            "Destructure an existential or sigma type hypothesis. \
             Introduces the witness and proof as separate hypotheses.",
            &["obtain \\<x, hx\\> := h"], &["rcases", "existsi"]),
        doc("tauto", Logic, "tauto",
            "Prove tautologies in propositional logic by exhaustive case analysis.",
            &["tauto"], &["decide", "itauto", "contradiction"]),
    ]
}

fn arithmetic_docs() -> Vec<TacticDoc> {
    use TacticCategory::Arithmetic;
    vec![
        doc(
            "omega",
            Arithmetic,
            "omega",
            "Solve linear arithmetic goals over natural numbers and integers. \
             Handles equalities, inequalities, and divisibility (Presburger arithmetic).",
            &["omega"],
            &["cert_mathverse", "linarith", "norm_num", "ring"],
        ),
        doc(
            "cert_mathverse",
            Arithmetic,
            "cert_mathverse",
            "Normalize certificate/list arithmetic wrappers, safely coerce supported Nat \
             linear goals toward Int form, then call omega with structured blocker diagnostics.",
            &["cert_mathverse"],
            &["cert_simp", "omega", "linarith", "norm_num"],
        ),
        doc(
            "norm_num",
            Arithmetic,
            "norm_num [ext : term*]",
            "Normalize numeric expressions and close numeric goals. Evaluates \
             arithmetic operations on concrete numbers.",
            &["norm_num", "norm_num [Nat.prime_def_lt_prime]"],
            &["omega", "ring", "simp"],
        ),
        doc(
            "ring",
            Arithmetic,
            "ring",
            "Prove equalities in commutative (semi)rings by normalizing both sides \
             to canonical polynomial form and comparing.",
            &["ring"],
            &["ring_nf", "linarith", "norm_num"],
        ),
        doc(
            "ring_nf",
            Arithmetic,
            "ring_nf",
            "Normalize ring expressions without closing the goal. Puts expressions \
             into canonical polynomial form.",
            &["ring_nf"],
            &["ring", "norm_num", "simp"],
        ),
        doc(
            "linarith",
            Arithmetic,
            "linarith [extra : term*]",
            "Prove linear arithmetic inequalities by finding a non-negative linear \
             combination of hypotheses that yields a contradiction (Farkas lemma).",
            &["linarith", "linarith [h1, h2]"],
            &["omega", "nlinarith", "norm_num"],
        ),
        doc(
            "nlinarith",
            Arithmetic,
            "nlinarith [extra : term*]",
            "Prove nonlinear arithmetic goals by generating polynomial witnesses. \
             Extends `linarith` with multiplication of hypotheses.",
            &["nlinarith", "nlinarith [sq_nonneg x]"],
            &["linarith", "polyrith", "positivity"],
        ),
        doc(
            "positivity",
            Arithmetic,
            "positivity",
            "Prove that an expression is nonneg or positive by recursively analyzing structure.",
            &["positivity"],
            &["nlinarith", "norm_num"],
        ),
        doc(
            "polyrith",
            Arithmetic,
            "polyrith",
            "Prove polynomial arithmetic goals using Groebner basis computation.",
            &["polyrith"],
            &["ring", "nlinarith", "linarith"],
        ),
        doc(
            "field_simp",
            Arithmetic,
            "field_simp [lemmas : term*]",
            "Clear denominators in field expressions. Rewrites division and inverse \
             operations to produce an equivalent goal without fractions.",
            &["field_simp"],
            &["ring", "norm_num", "simp"],
        ),
        doc(
            "cert_simp",
            Arithmetic,
            "cert_simp",
            "Simplify certificate, list, SAT/PB, and NN verification arithmetic wrappers \
             using the checked project lemma pack.",
            &["cert_simp"],
            &["cert_mathverse", "simp", "simp_all"],
        ),
    ]
}

fn search_docs() -> Vec<TacticDoc> {
    use TacticCategory::Search;
    vec![
        doc("aesop", Search, "aesop (config : AesopConfig?)",
            "Automated proof search using extensible rule sets. Performs a best-first search \
             over applicable lemmas, rewrite rules, and sub-tactics.",
            &["aesop"], &["decide", "library_search", "tauto"]),
        doc("decide", Search, "decide",
            "Solve decidable propositions by kernel reduction. Evaluates the `Decidable` instance.",
            &["decide"], &["native_decide", "omega", "tauto"]),
        doc("library_search", Search, "library_search",
            "Search the environment for a single lemma that closes the goal (via `exact` or `apply`).",
            &["library_search"], &["aesop", "exact?", "apply?"]),
        doc("exact?", Search, "exact?",
            "Search for an exact proof term that closes the goal. Suggests the term if found.",
            &["exact?"], &["apply?", "library_search"]),
        doc("apply?", Search, "apply?",
            "Search for a lemma that can be applied to make progress on the goal.",
            &["apply?"], &["exact?", "library_search"]),
    ]
}

fn combinator_docs() -> Vec<TacticDoc> {
    use TacticCategory::Combinator;
    vec![
        doc("repeat", Combinator, "repeat (tac : tactic)",
            "Repeatedly apply `tac` until it fails, then succeed. Always succeeds.",
            &["repeat intro _", "repeat (first | assumption | apply h)"],
            &["try", "all_goals", "any_goals"]),
        doc("try", Combinator, "try (tac : tactic)",
            "Try to apply `tac`. If it fails, succeed without changing the proof state.",
            &["try assumption", "try simp"], &["repeat", "first", "all_goals"]),
        doc("all_goals", Combinator, "all_goals (tac : tactic)",
            "Apply `tac` to every open goal. Fails if `tac` fails on any goal.",
            &["all_goals simp", "all_goals intro _"], &["any_goals", "focus", "try"]),
        doc("any_goals", Combinator, "any_goals (tac : tactic)",
            "Apply `tac` to every open goal. Succeeds if `tac` succeeds on at least one.",
            &["any_goals assumption"], &["all_goals", "try", "first"]),
        doc("first", Combinator, "first | tac1 | tac2 | ...",
            "Try each tactic in order. Succeed with the first that succeeds. Fail if all fail.",
            &["first | assumption | trivial | simp"], &["try", "repeat", "all_goals"]),
        doc("focus", Combinator, "focus (tac : tactic)",
            "Apply `tac` focusing on the first goal only. Other goals are hidden and restored after.",
            &["focus (intro h; exact h)"], &["all_goals", "swap", "rotate"]),
    ]
}

fn closing_docs() -> Vec<TacticDoc> {
    use TacticCategory::Closing;
    vec![
        doc("rfl", Closing, "rfl",
            "Close the goal by reflexivity. Works when the goal is `a = a` or any reflexive relation.",
            &["rfl"], &["exact rfl", "symm", "Eq.refl"]),
        doc("trivial", Closing, "trivial",
            "Close the goal using simple tactics: `rfl`, `assumption`, `contradiction`, constructors.",
            &["trivial"], &["assumption", "rfl", "decide"]),
        doc("sorry", Closing, "sorry",
            "Admit the current goal without proof. WARNING: using `sorry` makes the proof unsound.",
            &["sorry"], &["admit"]),
        doc("done", Closing, "done",
            "Assert that there are no remaining goals. Fails if any goals are still open.",
            &["done"], &["trivial", "rfl"]),
    ]
}

fn advanced_docs() -> Vec<TacticDoc> {
    use TacticCategory::Advanced;
    vec![
        doc("conv", Advanced, "conv => (conv_tactics)",
            "Enter conversion mode to rewrite specific subexpressions. \
             Navigate with `lhs`, `rhs`, `arg`, `ext`, then apply rewrites.",
            &["conv => rw [h]", "conv in (f _) => rw [h]"], &["rw", "simp", "change"]),
        doc("calc", Advanced, "calc a R1 b := ... _ R2 c := ...",
            "Structured proof by a chain of relation steps composed transitively.",
            &["calc x = y := by rfl\n  _ < z := by linarith"], &["trans", "conv"]),
        doc("induction", Advanced, "induction (e : term) with cases",
            "Perform structural induction on a variable. Creates one subgoal per constructor \
             with induction hypotheses for recursive arguments.",
            &["induction n with | zero => ... | succ n ih => ..."],
            &["cases", "rcases", "inductive_reasoning"]),
        doc("generalize", Advanced, "generalize (h : Name?) : e = x",
            "Replace a subexpression `e` in the goal with a fresh variable `x`, \
             optionally adding `h : e = x` as a hypothesis.",
            &["generalize h : f x = y"], &["revert", "intro", "specialize"]),
        doc("have", Advanced, "have (h : Name) : (type : term) := proof",
            "Introduce an intermediate assertion. Proves `type` as a subgoal, \
             then adds `h : type` to the context for the remaining proof.",
            &["have h : n > 0 := by omega"], &["let", "suffices", "show"]),
        doc("suffices", Advanced, "suffices (h : Name) : (type : term) by tac",
            "Assert that proving `type` suffices to close the current goal.",
            &["suffices h : P by exact h"], &["have", "show"]),
        doc("revert", Advanced, "revert (names : Name*)",
            "Move hypotheses from the context back into the goal as forall binders. Inverse of `intro`.",
            &["revert h", "revert x y"], &["intro", "generalize", "clear"]),
        doc("specialize", Advanced, "specialize (h : Name) (args : term*)",
            "Specialize a hypothesis by providing arguments. \
             Replaces `h : forall x, P x` with `h : P a` after `specialize h a`.",
            &["specialize h 42", "specialize h x rfl"], &["have", "apply", "revert"]),
        doc("subst", Advanced, "subst (h : Name)",
            "Substitute an equality hypothesis `h : x = e` throughout the goal and context.",
            &["subst h", "subst_vars"], &["rw", "simp"]),
        doc("monad_pres", Advanced, "monad_pres [field1, field2, ...]",
            "Prove that a monadic computation preserves specified state fields. \
             Decomposes `StateT` bind chains into per-step preservation obligations. \
             Handles `ite`/`dite` case splits and `Except.casesOn` by checking each \
             branch independently. Steps that are definitionally equal are closed by refl; \
             non-trivial steps are left as subgoals.",
            &["monad_pres [memory]", "monad_pres [memory, permissions]"],
            &["simp", "rfl", "conv"]),
    ]
}
