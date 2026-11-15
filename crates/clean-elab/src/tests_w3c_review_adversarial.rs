// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial arms for the two fixes whose own pins assert only the shapes
//! they REPAIR: the commutative-`max` level postponement
//! (`tests_imported_max_level_instance.rs`) and the `classical` scope carried
//! into simp's instance-slot synthesis (`tests_classical_scope_simp.rs`).
//!
//! Both fixes WIDEN what is accepted, so each needs the refusal beside it.
//! The `max` half is pinned at the SOLVER, not through an instance, because
//! an instance fixture cannot exhibit an unsatisfiable ambiguous `max`: a
//! candidate whose class level disagrees with its conclusion's sort does not
//! kernel-check in the first place (measured — the first draft of these arms
//! died in `add_decl`).
//!
//! The `classical` half carries its own experiment. A first draft asserted
//! that a `classical` opened in a nested `by` block does not scope the outer
//! block's `simp`, read zero errors, and would have been filed as a leak.
//! Two controls refuted that: the outer block really does continue past the
//! nested block (`..._probe_outer_block_continues`), the counter really is
//! restored (`..._outer_exact_reads_the_counter`), and a hypothesis of the
//! outer goal's own statement closes `simp only` here with no `classical`
//! anywhere (`..._diverging_from_lean`). With that confound removed the arm
//! passes: there is no leak.

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Environment;

// -- the commutative-`max` postponement, fail-closed ------------------------

/// `max (?a+1) (?b+1) =?= max (u+1) (v+1)` with `u`/`v` RIGID: both pairings
/// solve it, so the solver must POSTPONE and assign nothing. The positional
/// split used to commit `?a := u`, `?b := v` here, and the argument
/// unification that follows — `Prod.{?a, ?b} =?= Prod.{u, v}` in the goal's
/// own order, or the crossed order a decoded `.olean` candidate arrives in —
/// then had no way back.
#[test]
fn test_ambiguous_max_pairing_is_postponed_and_assigns_nothing() {
    use crate::unify::level_solve::solve_level_eq;
    use crate::unify::MetaState;
    use crate::unify::UnifyResult;

    let mut metas = MetaState::new();
    metas.set_rigid_level_params([Name::from_string("u"), Name::from_string("v")]);
    let lhs = Level::max(
        Level::succ(Level::param(Name::from_string("a"))),
        Level::succ(Level::param(Name::from_string("b"))),
    );
    let rhs = Level::max(
        Level::succ(Level::param(Name::from_string("u"))),
        Level::succ(Level::param(Name::from_string("v"))),
    );
    assert!(
        matches!(solve_level_eq(&mut metas, &lhs, &rhs), UnifyResult::Success),
        "an ambiguous `max` pairing is deferred, not refused"
    );
    assert_eq!(
        metas.postponed_level_count(),
        1,
        "it must be DEFERRED — a committed positional split would leave the queue empty"
    );
    assert_eq!(
        metas.instantiate_level(&Level::param(Name::from_string("a"))),
        Level::param(Name::from_string("a")),
        "nothing may be assigned while the pairing is a choice"
    );
}

/// FAIL-CLOSED, and the reason the arm above is allowed to return `Success`:
/// an ambiguous `max` the surrounding term then grounds INCONSISTENTLY must
/// fail at the declaration-boundary drain. Deferral is not acceptance.
#[test]
fn test_postponed_ambiguous_max_still_fails_closed_at_the_drain() {
    use crate::unify::level_solve::solve_level_eq;
    use crate::unify::MetaState;

    let mut metas = MetaState::new();
    metas.set_rigid_level_params([
        Name::from_string("u"),
        Name::from_string("v"),
        Name::from_string("w"),
    ]);
    let a = Level::param(Name::from_string("a"));
    let b = Level::param(Name::from_string("b"));
    let lhs = Level::max(Level::succ(a.clone()), Level::succ(b.clone()));
    let rhs = Level::max(
        Level::succ(Level::param(Name::from_string("u"))),
        Level::succ(Level::param(Name::from_string("v"))),
    );
    let _ = solve_level_eq(&mut metas, &lhs, &rhs);
    assert_eq!(metas.postponed_level_count(), 1);
    // The arguments pin a THIRD rigid universe: neither pairing can hold.
    let _ = solve_level_eq(&mut metas, &a, &Level::param(Name::from_string("w")));
    assert!(
        metas.drain_postponed_levels().is_err(),
        "a deferred `max` the term grounded inconsistently must ERROR at the \
         boundary; if this ever returns Ok the postponement is a hole"
    );
}

/// The drain CLOSES the crossed pairing once the arguments have pinned it —
/// the whole point of deferring. `max (v+1) (u+1)` and `max (u+1) (v+1)` are
/// the same level, so `Level::is_def_eq` settles it with nothing left over.
#[test]
fn test_postponed_ambiguous_max_is_discharged_by_the_crossed_grounding() {
    use crate::unify::level_solve::solve_level_eq;
    use crate::unify::MetaState;

    let mut metas = MetaState::new();
    metas.set_rigid_level_params([Name::from_string("u"), Name::from_string("v")]);
    let a = Level::param(Name::from_string("a"));
    let b = Level::param(Name::from_string("b"));
    let lhs = Level::max(Level::succ(a.clone()), Level::succ(b.clone()));
    let rhs = Level::max(
        Level::succ(Level::param(Name::from_string("u"))),
        Level::succ(Level::param(Name::from_string("v"))),
    );
    let _ = solve_level_eq(&mut metas, &lhs, &rhs);
    // The CROSSED grounding — what `Prod.{u, v}` forces when the candidate's
    // class level is Lean's normalised `max (v+1) (u+1)`.
    let _ = solve_level_eq(&mut metas, &a, &Level::param(Name::from_string("v")));
    let _ = solve_level_eq(&mut metas, &b, &Level::param(Name::from_string("u")));
    metas
        .drain_postponed_levels()
        .expect("the crossed grounding discharges the deferred equation");
}

/// NARROWNESS control. When only ONE pairing solves the equation there is no
/// choice to defer, so the componentwise split must still COMMIT in place —
/// that is what keeps every `max` whose operands pair one way (class (20)'s
/// `HasEquiv` family, class (16)'s `Compl`) on its pre-fix path.
#[test]
fn test_unambiguous_max_pairing_still_commits_in_place() {
    use crate::unify::level_solve::solve_level_eq;
    use crate::unify::MetaState;
    use crate::unify::UnifyResult;

    let mut metas = MetaState::new();
    metas.set_rigid_level_params([Name::from_string("u"), Name::from_string("v")]);
    let a = Level::param(Name::from_string("a"));
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    // `max(?a, u) =?= max(v, u)`: positional gives `?a := v`; swapped needs
    // `u := v` between two rigid params and cannot.
    let lhs = Level::max(a.clone(), u.clone());
    let rhs = Level::max(v.clone(), u.clone());
    assert!(
        matches!(solve_level_eq(&mut metas, &lhs, &rhs), UnifyResult::Success),
        "the unambiguous split must still succeed"
    );
    assert_eq!(
        metas.postponed_level_count(),
        0,
        "one solvable pairing is not a choice: it must be committed, not deferred"
    );
    assert_eq!(
        metas.instantiate_level(&a),
        v,
        "the committed split must have assigned the only solution"
    );
}

// -- the `classical` scope, non-leak ----------------------------------------

fn elab_in_file(src: &str) -> Vec<String> {
    use crate::tactic::builtins::builtin_tactic_patterns;
    use crate::{preprocess_decl_with_context, FileContext};
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = clean_parser::parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut errors = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        if let Err(e) =
            crate::elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        {
            errors.push(format!("{e:?}"));
        }
    }
    errors
}

const CLASSICAL_SIMP_PRELUDE: &str = "namespace Classical\n\
    noncomputable scoped instance (priority := low) propDecidable' (p : Prop) : Decidable p :=\n\
    \x20 Classical.choice (match Classical.em p with\n\
    \x20   | Or.inl h => ⟨Decidable.isTrue h⟩\n\
    \x20   | Or.inr h => ⟨Decidable.isFalse h⟩)\n\
    end Classical\n\
    axiom Q : Nat → Prop\n\
    axiom g : Nat → Nat\n\
    axiom gdef (n : Nat) [inst : Decidable (Q n)] : g n = 1\n";

/// `classical` must not survive the declaration that opens it. The depth is
/// now RE-PUBLISHED to the `ProofState` on every change, so a restore that
/// forgot to republish — or a counter that is never decremented — would show
/// up here as a second theorem that suddenly needs no `classical`.
///
/// Exactly one error is required: the SECOND theorem's, and not the first's.
#[test]
fn test_classical_does_not_leak_into_the_next_declaration() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem withClassical (n : Nat) : g n = 1 := by\n\
         \x20 classical\n\
         \x20 simp only [gdef]\n\
         theorem afterClassical (n : Nat) : g n = 1 := by\n\
         \x20 simp only [gdef]\n"
    );
    let errors = elab_in_file(&src);
    assert_eq!(
        errors.len(),
        1,
        "`classical` must be scoped to the block that opens it, so exactly the \
         second theorem fails: {errors:?}"
    );
}

/// The CONTROL for the arm above: the same outer `simp only [gdef]` after a
/// `have` whose own block opens NO `classical`. It must fail. Without this,
/// a nested arm reporting zero errors could be read as a leak when the outer
/// simp simply never needed the instance.
#[test]
fn test_outer_simp_after_a_plain_have_still_needs_classical() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem plainHave (n : Nat) : g n = 1 := by\n\
         \x20 have h : Nat = Nat := rfl\n\
         \x20 simp only [gdef]\n"
    );
    let errors = elab_in_file(&src);
    assert_eq!(
        errors.len(),
        1,
        "with no `classical` anywhere the outer simp must still fail: {errors:?}"
    );
}

/// Nesting probe: does the OUTER block really continue after the `have`'s own
/// `by` block? `h` is bound only in the outer block, so `exact h` succeeds
/// exactly when the parser kept the two blocks apart. Without this the
/// arm above cannot tell a scope leak from a flattened parse.
#[test]
fn test_nested_by_block_probe_outer_block_continues() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem nestProbe (n : Nat) : g n = 1 := by\n\
         \x20 have h : g n = 1 := by\n\
         \x20   classical\n\
         \x20   simp only [gdef]\n\
         \x20 exact h\n"
    );
    let errors = elab_in_file(&src);
    assert!(
        errors.is_empty(),
        "the outer block must continue after the nested `by` (else the nesting \
         arms measure a parse, not a scope): {errors:?}"
    );
}

/// Which half leaks: the `ElabCtx` DEPTH COUNTER or the published
/// `InstanceVisibility`? The term path (`exact`) reads
/// `ElabCtx::classical_tactic_scope` directly, so this arm succeeding means
/// the counter itself survived the nested block.
#[test]
fn test_nested_classical_then_outer_exact_reads_the_counter() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem nestExact (n : Nat) : g n = 1 := by\n\
         \x20 have h : Nat = Nat := by\n\
         \x20   classical\n\
         \x20   rfl\n\
         \x20 exact gdef n\n"
    );
    let errors = elab_in_file(&src);
    assert_eq!(
        errors.len(),
        1,
        "a nested `classical` must not leave the counter open for the outer \
         block's term path: {errors:?}"
    );
}

/// A second consumer whose statement the nested `have`'s hypothesis cannot
/// close, so the outer block's simp genuinely needs the instance.
const SECOND_CONSUMER: &str = "axiom g2 : Nat → Nat\n\
    axiom g2def (n : Nat) [inst : Decidable (Q n)] : g2 n = 1\n\
    axiom gplain (n : Nat) : g n = 1\n";

/// The control that makes the nested-`classical` arm below interpretable,
/// and a CLOSED divergence (G49, ledger (119)).
///
/// Pinned `lean` v4.30.0-rc2 REFUSES this file with "`simp` made no progress":
/// `simp only [gdef]` cannot synthesize `[Decidable (Q n)]`, and a local
/// hypothesis of exactly the goal's statement does not close a `simp only`
/// for it — hypotheses reach simp only through `simp [*]` / `simp_all` / an
/// explicit `simp only [.., h]`. Clean closed it with an `assumption` step
/// Lean's simp does not have; since G49 it refuses it as Lean does. With a
/// hypothesis of the outer goal's own statement in context, zero errors would
/// say nothing about which instances were visible — which is why this row
/// sits beside the arm below.
#[test]
fn test_simp_only_does_not_close_from_a_matching_hypothesis() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}{SECOND_CONSUMER}theorem hypConfound (n : Nat) : g n = 1 := by\n\
         \x20 have h : g n = 1 := gplain n\n\
         \x20 simp only [gdef]\n"
    );
    let errors = elab_in_file(&src);
    let rendered = format!("{errors:?}");
    assert!(
        !errors.is_empty() && rendered.contains("NoProgress"),
        "pinned Lean answers \"`simp` made no progress\"; Clean must not close the goal \
         from the unnamed hypothesis: {rendered}"
    );
}

/// The nested-leak arm with the confound removed: the outer goal is `g2 n = 1`
/// and the nested `have` proves `g n = 1`, which cannot close it. A
/// `classical` opened inside the `have`'s own block must not scope the outer
/// block's simp.
#[test]
fn test_nested_classical_does_not_scope_a_disjoint_outer_simp() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}{SECOND_CONSUMER}theorem nestDisjoint (n : Nat) : g2 n = 1 := by\n\
         \x20 have h : g n = 1 := by\n\
         \x20   classical\n\
         \x20   simp only [gdef]\n\
         \x20 simp only [g2def]\n"
    );
    let errors = elab_in_file(&src);
    assert_eq!(
        errors.len(),
        1,
        "a `classical` opened in a nested `by` block must not stay published on \
         the OUTER proof state: {errors:?}"
    );
}
