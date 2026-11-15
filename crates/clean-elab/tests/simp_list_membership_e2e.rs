// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! trust-ir gap G25, ledger class (94): the default `simp` set rewrites List
//! membership as Lean 4.8.0's does.
//!
//! Pinned Lean 4.8.0 (`set_option trace.Meta.Tactic.simp.rewrite true`)
//! rewrites `c ∈ [1, 2]` with `@List.mem_cons:1000` twice and closes the tail
//! with `@List.not_mem_nil:1000`; `(← getSimpTheorems).isLemma (.decl n)` over
//! every `List.*mem*` constant answers exactly `List.mem_cons`,
//! `List.not_mem_nil` and `List.mem_map`. With the builtin prelude Clean made
//! no progress: the prelude declared both theorems but registered no
//! `@[simp]` attribute for them, and `List.not_mem_nil` was stated over the
//! raw `List.Mem` where Lean states it through `∈`, so even
//! `simp [List.not_mem_nil]` could not rewrite `c ∈ []`. The prelude now
//! registers the attribute WITH each declaration (`init_multiset_mem`,
//! `init_finset_mem_empty`), so it behaves as an attribute: `simp only` at the
//! goal or at a hypothesis leaves it out, and `simp [-n]` and
//! `attribute [-simp] n` erase it.
//!
//! Every source below was run through the pinned binary
//! (`~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean`): the accepted
//! theorems check there, and each refused one is refused there, with the
//! error quoted beside it.

use std::collections::BTreeSet;

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::expr::ExprKind;
use clean_kernel::{Environment, Expr, Name};
use clean_parser::parse_file;

/// Elaborate and kernel-register every declaration in `source`, failing on
/// any `Failed` leaf of an `ElabResult::Multiple`.
fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failures(result: &ElabResult) -> Result<(), String> {
        match result {
            ElabResult::Multiple(results) => results.iter().try_for_each(failures),
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

/// `source` must register, and every theorem named in `names` must close
/// over the foundational axioms only (no `sorryAx`, no domain axiom).
fn accepts(source: &str, names: &[&str]) {
    let mut env = Environment::with_prelude();
    register(&mut env, source).unwrap_or_else(|error| panic!("must elaborate: {error}"));
    let foundational: BTreeSet<Name> = ["propext", "Quot.sound", "Classical.choice"]
        .into_iter()
        .map(Name::from_string)
        .collect();
    for name in names {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        let extra: Vec<&Name> = deps.iter().filter(|d| !foundational.contains(*d)).collect();
        assert!(
            extra.is_empty(),
            "`{name}` closed over non-foundational axioms {extra:?}"
        );
    }
}

/// `source` must be refused for its meaning (it parses) with an error that
/// matches `needle`, and `name` must not be registered.
fn refuses(source: &str, name: &str, needle: &str) {
    let mut env = Environment::with_prelude();
    let error = register(&mut env, source).expect_err("pinned Lean 4.8.0 refuses this");
    assert!(!error.contains("parse error"), "must parse: {error}");
    assert!(
        !error.to_lowercase().contains("sorryax"),
        "no sorry fallback: {error}"
    );
    assert!(
        error.contains(needle),
        "refused, but not for the expected reason `{needle}`: {error}"
    );
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "`{name}` was registered anyway"
    );
}

/// The trust-ir shape (`Proofs/AggregateProps.lean` `vector_*_const_typing`):
/// `simp at hc` turns membership in a literal list into its disjunction.
#[test]
fn test_simp_default_set_rewrites_list_literal_membership() {
    accepts(
        "inductive K where\n  | a : Nat → K\n  | b : Bool → K\n\n\
         theorem g25_cons (c : K) (hc : c ∈ [K.a 1, K.a 2, K.b true]) :\n    \
         c = K.a 1 ∨ c = K.a 2 ∨ c = K.b true := by\n  simp at hc\n  exact hc\n",
        &["g25_cons"],
    );
}

/// `simp at h` and `simpa … using h` run to a FIXPOINT, as Lean's `Simp.main`
/// does: one traversal stopped at `c = 1 ∨ c ∈ [2, 3]`, never revisiting the
/// membership its first rewrite produced.
#[test]
fn test_simp_at_hypothesis_reaches_fixpoint() {
    accepts(
        "theorem g25_three (c : Nat) (hc : c ∈ [1, 2, 3]) : c = 1 ∨ c = 2 ∨ c = 3 := by\n  \
         simp at hc\n  exact hc\n\
         theorem g25_simpa (c : Nat) (hc : c ∈ [1, 2, 3]) : c = 1 ∨ c = 2 ∨ c = 3 := by\n  \
         simpa using hc\n",
        &["g25_three", "g25_simpa"],
    );
}

/// NEGATIVE: the fixpoint is the whole three-way disjunction. Pinned Lean
/// 4.8.0: `type mismatch … has type c = 1 ∨ c = 2 ∨ c = 3 : Prop but is
/// expected to have type c = 1 ∨ c = 2 : Prop`.
#[test]
fn test_simpa_fixpoint_is_not_a_shorter_disjunction() {
    refuses(
        "theorem g25_three_twin (c : Nat) (hc : c ∈ [1, 2, 3]) : c = 1 ∨ c = 2 := by\n  \
         simpa using hc\n",
        "g25_three_twin",
        "Or vs Eq",
    );
}

/// `c ∈ [c]` and `c ∈ [d, c]` close (`mem_cons`, `eq_self`, `not_mem_nil`,
/// `or_false`/`or_true`), and a hypothesis `c ∈ []` closes the goal.
#[test]
fn test_simp_default_set_closes_membership_goals() {
    accepts(
        "theorem g25_self (c : Nat) : c ∈ [c] := by simp\n\
         theorem g25_tail (c d : Nat) : c ∈ [d, c] := by simp\n\
         theorem g25_nil (c : Nat) (h : c ∈ ([] : List Nat)) : False := by simp at h\n",
        &["g25_self", "g25_tail", "g25_nil"],
    );
}

/// `List.not_mem_nil` and `List.mem_cons` carry Lean's statements: both
/// `@`-forms check against Lean 4.8.0's printed types.
#[test]
fn test_list_membership_lemma_statements_are_leans() {
    accepts(
        "theorem nmn_stmt : ∀ {α : Type} (a : α), ¬ a ∈ ([] : List α) := @List.not_mem_nil\n\
         theorem mc_stmt : ∀ {α : Type} {a b : α} {l : List α},\n    \
         a ∈ b :: l ↔ a = b ∨ a ∈ l := @List.mem_cons\n",
        &["nmn_stmt", "mc_stmt"],
    );
}

/// The STORED statement of `List.not_mem_nil` is Lean's `¬ a ∈ []` — the
/// `Membership.mem` head simp matches — not the definitionally equal raw
/// `¬ List.Mem a []` the prelude used to state (which every check above would
/// also accept, by unfolding the reducible instance). Its printed form is the
/// Lean side of the `List.not_mem_nil` row `data/prelude_collision_census.json`
/// recorded before this change.
#[test]
fn test_not_mem_nil_stored_statement_is_membership_form() {
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("List.not_mem_nil"))
        .expect("the prelude declares List.not_mem_nil");
    let mut body = &info.type_;
    let mut binders = 0;
    while let ExprKind::Pi(_, _, codomain) = body.kind() {
        binders += 1;
        body = codomain;
    }
    assert_eq!(binders, 2, "{{α}} (a : α): {}", info.type_);
    let head_name = |e: &Expr| match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.to_string()),
        _ => None,
    };
    assert_eq!(head_name(body).as_deref(), Some("Not"), "{}", info.type_);
    let prop: &Expr = body.get_app_args()[0];
    assert_eq!(
        head_name(prop).as_deref(),
        Some("Membership.mem"),
        "List.not_mem_nil must be stated through `∈`: {}",
        info.type_
    );
    let args = prop.get_app_args();
    assert_eq!(args.len(), 5, "{}", info.type_);
    assert_eq!(head_name(args[2]).as_deref(), Some("List.instMembership"));
    assert_eq!(head_name(args[3]).as_deref(), Some("List.nil"));
}

/// NEGATIVE: a false membership claim. Pinned Lean 4.8.0: `unsolved goals ⊢
/// False` (simp reduces `3 ∈ [1, 2]` to `False` and cannot close it).
#[test]
fn test_simp_false_membership_is_refused() {
    refuses(
        "theorem g25_twin_false : (3 : Nat) ∈ [1, 2] := by simp\n",
        "g25_twin_false",
        "unsolved goals",
    );
}

/// NEGATIVE, right reason: the rewritten hypothesis is the WHOLE disjunction,
/// not one disjunct. Pinned Lean 4.8.0: `type mismatch … hc has type c = 1 ∨
/// c = 2 : Prop but is expected to have type c = 1 : Prop`.
#[test]
fn test_simp_membership_rewrite_is_the_disjunction() {
    refuses(
        "theorem g25_twin (c : Nat) (hc : c ∈ [1, 2]) : c = 1 := by\n  simp at hc\n  exact hc\n",
        "g25_twin",
        "Or",
    );
}

/// NEGATIVE: the lemmas are in the DEFAULT set only. Pinned Lean 4.8.0 says
/// `simp made no progress` for each of these: `simp only []` starts from
/// `eq_self`/`iff_self`, and `-name` erases the lemma.
#[test]
fn test_membership_lemmas_absent_from_simp_only_and_erasable() {
    refuses(
        "theorem only_ctl (c : Nat) : c ∈ [c] := by simp only []\n",
        "only_ctl",
        "no progress",
    );
    refuses(
        "theorem erase_ctl (c : Nat) : c ∈ [c] := by simp [-List.mem_cons]\n",
        "erase_ctl",
        "no progress",
    );
    refuses(
        "theorem erase_nil_ctl (c : Nat) (h : c ∈ ([] : List Nat)) : False := by\n  \
         simp [-List.not_mem_nil] at h\n",
        "erase_nil_ctl",
        "no progress",
    );
}

/// NEGATIVE: `simp only … at h` is `only` too. The hypothesis path dropped
/// the flag and ran the whole default set, so each of these was accepted.
/// Pinned Lean 4.8.0: "simp made no progress" for the first two; for the
/// third, `type mismatch … hc has type c = 1 ∨ c = 2 ∨ c ∈ []` (only
/// `mem_cons` fires, so the nil tail is left).
#[test]
fn test_simp_only_at_hypothesis_excludes_default_set() {
    refuses(
        "theorem only_at_ctl (c : Nat) (hc : c ∈ [1, 2]) : c = 1 ∨ c = 2 := by\n  \
         simp only [] at hc\n  exact hc\n",
        "only_at_ctl",
        "no progress",
    );
    refuses(
        "theorem only_at_unrelated (c : Nat) (hc : c ∈ [1, 2]) : c = 1 ∨ c = 2 := by\n  \
         simp only [Nat.add_zero] at hc\n  exact hc\n",
        "only_at_unrelated",
        "no progress",
    );
    refuses(
        "theorem only_at_cons (c : Nat) (hc : c ∈ [1, 2]) : c = 1 ∨ c = 2 := by\n  \
         simp only [List.mem_cons] at hc\n  exact hc\n",
        "only_at_cons",
        "mismatch",
    );
}

/// POSITIVE twin of the `only` controls: naming the rules makes `simp only …
/// at h` do the rewrite. Pinned Lean 4.8.0 accepts it. (The `at *` spelling
/// is not used here: Clean's `simp at *` closes a goal that equals a
/// rewritten hypothesis, which Lean's does not; see ledger class (94).)
#[test]
fn test_simp_only_at_hypothesis_uses_named_rules() {
    accepts(
        "theorem only_at_named (c : Nat) (hc : c ∈ [1, 2]) : c = 1 ∨ c = 2 := by\n  \
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hc\n  exact hc\n",
        &["only_at_named"],
    );
}

/// `attribute [-simp]` erases the prelude's attribute as it erases any other.
/// Pinned Lean 4.8.0 accepts the erasure itself, then says "simp made no
/// progress" once the erased lemma is the one the proof needed; naming it
/// again (`simp [List.mem_cons]`) closes the goal.
#[test]
fn test_attribute_erase_removes_membership_lemmas() {
    refuses(
        "attribute [-simp] List.mem_cons\n\
         theorem erased_cons (c : Nat) : c ∈ [c] := by simp\n",
        "erased_cons",
        "no progress",
    );
    refuses(
        "attribute [-simp] List.not_mem_nil\n\
         theorem erased_nil (c : Nat) (h : c ∈ ([] : List Nat)) : False := by\n  simp at h\n",
        "erased_nil",
        "no progress",
    );
    accepts(
        "attribute [-simp] List.mem_cons\n\
         theorem erased_back (c : Nat) : c ∈ [c] := by simp [List.mem_cons]\n",
        &["erased_back"],
    );
}

/// NEGATIVE: `simp … at h` whose rewriting never terminates is refused, as
/// Lean refuses it (pinned 4.8.0: "maximum recursion depth has been
/// reached"). The hypothesis fixpoint used to hand back what its last
/// traversal left (`f 1000 = 5`) and accept.
#[test]
fn test_simp_at_hypothesis_without_fixpoint_is_refused() {
    refuses(
        "theorem runaway (f : Nat → Nat) (h1 : ∀ x, f x = f (x + 1)) (h : f 0 = 5) : True := by\n  \
         simp [h1] at h\n  trivial\n",
        "runaway",
        "no fixpoint",
    );
}

/// CLOSED at the round-3/4 integration (integ/r5, 2026-10-16), pinned as a
/// refusal until then. Lean 4.8.0 closes `¬ c ∈ []` with `@List.not_mem_nil`
/// then `not_false_eq_true` (`trace.Meta.Tactic.simp.rewrite`); both are
/// `@[simp]` there. The prelude had no `not_false_eq_true`, so Clean stopped at
/// `¬False`; lane T's G39 (decision R50) declares it, and the merged tree
/// closes the goal as Lean does. The false twin `c ∈ []` is refused as Lean
/// refuses it ("unsolved goals ⊢ False").
#[test]
fn test_simp_not_mem_nil_goal_closes() {
    accepts(
        "theorem nil_goal (c : Nat) : ¬ c ∈ ([] : List Nat) := by simp\n",
        &["nil_goal"],
    );
    refuses(
        "theorem nil_false (c : Nat) : c ∈ ([] : List Nat) := by simp\n",
        "nil_false",
        "unsolved goals",
    );
}

/// CLOSED at the round-3/4 integration (integ/r5, 2026-10-16) — was a KNOWN
/// DIVERGENCE (ACCEPTED, LEAN REFUSES), pinned 2026-10-08.
/// `List.mem_singleton` is not a Lean 4.8.0 core constant (pinned: `unknown
/// constant 'List.mem_singleton'`; it is Std/Batteries'), and the builtin
/// prelude does not declare it. Clean used to warn and drop a simp argument
/// that names nothing, so G25's membership rules closed the goal; lane T's
/// G48 (decision R48) refuses it as Lean's `elabSimpArgs` does, so the merged
/// tree is Lean's refusal. The control without the name still closes.
#[test]
fn test_simp_unknown_lemma_name_is_refused() {
    let env = Environment::with_prelude();
    assert!(
        env.get_const(&Name::from_string("List.mem_singleton"))
            .is_none(),
        "List.mem_singleton is not Lean 4.8.0 core; the prelude must not declare it"
    );
    refuses(
        "theorem singleton_ctl (c : Nat) : c ∈ [c] := by simp [List.mem_singleton]\n",
        "singleton_ctl",
        "unknown identifier: List.mem_singleton",
    );
    accepts(
        "theorem singleton_ok (c : Nat) : c ∈ [c] := by simp\n",
        &["singleton_ok"],
    );
}
