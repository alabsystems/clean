// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for the `|` alternation's per-branch FIELD LOCATION in
//! `rcases`/`obtain`/`rintro` (RC-L).
//!
//! `split_or_hypothesis` used to read each branch's constructor field as the
//! branch context's `.last()` declaration. That is only ever right for a
//! one-field constructor whose branch context ends with that field:
//!
//! * a NULLARY constructor (`Nat.zero`, `Option.none`, `List.nil`) appends no
//!   field at all, so `.last()` either found nothing (a hard
//!   `HypothesisNotFound` error for the whole tactic) or — worse — picked up an
//!   unrelated OUTER hypothesis and renamed it;
//! * a MULTI-field constructor (`List.cons`) appends several, so `.last()` found
//!   the LAST field and a `⟨x, xs⟩` pattern was applied to it instead of being
//!   spread across the fields.
//!
//! The fix indexes fields by the count `cases` actually appended to that branch
//! (`branch_ctx_len - (ctx_len_before - 1)`), for which 0 is a legal answer.

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

use super::core::ProofState;
use super::pattern::destruct_named_hypothesis;
use super::proof_term::intro;

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// `rcases n with _ | m` on the ONLY hypothesis in context: the `Nat.zero`
/// branch legitimately binds no field, and the whole tactic must still succeed.
///
/// Before the fix the zero branch's context was empty, `.last()` returned
/// `None`, and the tactic failed with "case-split branch produced no field
/// hypothesis" — so the single most common `Nat` destructuring idiom
/// (`obtain _ | n := n`) could not run at all.
#[test]
fn test_rcases_alternation_nullary_branch_binds_nothing() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let mut state = ProofState::new(env, Expr::arrow(nat_ty(), nat_ty()));
    intro(&mut state, "n").expect("intro n");

    destruct_named_hypothesis(&mut state, "n", "_ | m")
        .expect("`rcases n with _ | m` must split Nat even though Nat.zero binds no field");

    assert_eq!(
        state.goals().len(),
        2,
        "Nat split should leave one goal per constructor, got {:?}",
        state.goals()
    );
    assert!(
        state.goals()[0].local_ctx.is_empty(),
        "the Nat.zero branch binds no field, so its context must stay empty, got {:?}",
        state.goals()[0].local_ctx
    );
    let succ_ctx = &state.goals()[1].local_ctx;
    assert_eq!(
        succ_ctx.len(),
        1,
        "the Nat.succ branch must carry exactly its one field, got {succ_ctx:?}"
    );
    assert_eq!(
        succ_ctx[0].name, "m",
        "the Nat.succ field must take the second alternative's name"
    );
}

/// The nullary branch must not touch an unrelated OUTER hypothesis.
///
/// Before the fix, `.last()` on the zero branch's context returned the outer
/// `hp` (the scrutinee having been removed), so the first alternative's name was
/// silently written over `hp` — a wrong context, reported as success.
#[test]
fn test_rcases_alternation_nullary_branch_does_not_rename_outer_hypothesis() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    let true_ty = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, Expr::arrow(true_ty, Expr::arrow(nat_ty(), nat_ty())));
    intro(&mut state, "hp").expect("intro hp");
    intro(&mut state, "n").expect("intro n");

    destruct_named_hypothesis(&mut state, "n", "hz | m")
        .expect("`rcases n with hz | m` must split Nat");

    assert_eq!(state.goals().len(), 2, "Nat split should leave two goals");
    let zero_ctx = &state.goals()[0].local_ctx;
    assert_eq!(
        zero_ctx.len(),
        1,
        "the Nat.zero branch keeps only the outer hypothesis, got {zero_ctx:?}"
    );
    assert_eq!(
        zero_ctx[0].name, "hp",
        "the outer hypothesis must keep its name — a nullary branch's pattern has \
         no field to bind and must never rename an unrelated hypothesis"
    );
    let succ_ctx = &state.goals()[1].local_ctx;
    assert_eq!(
        succ_ctx.len(),
        2,
        "the Nat.succ branch keeps the outer hypothesis plus its field, got {succ_ctx:?}"
    );
    assert_eq!(succ_ctx[0].name, "hp", "outer hypothesis stays first");
    assert_eq!(
        succ_ctx[1].name, "m",
        "the Nat.succ field takes the second alternative's name"
    );
}

/// `rcases l with _ | ⟨x, xs⟩` on a `List`: the `List.cons` branch has TWO
/// fields, so the tuple pattern maps positionally over them (Lean's rcases:
/// "naming the first three parameters of the first constructor as `a,b,c`").
///
/// Before the fix the tuple was applied to `.last()` — the tail field — and the
/// tactic failed with "pattern has 2 components but hypothesis 'cons_1' is not
/// destructurable".
#[test]
fn test_rcases_alternation_multi_field_branch_maps_tuple_over_fields() {
    let env = Environment::with_prelude();
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![clean_kernel::Level::zero()]),
        nat_ty(),
    );
    let mut state = ProofState::new(env, Expr::arrow(list_nat, nat_ty()));
    intro(&mut state, "l").expect("intro l");

    destruct_named_hypothesis(&mut state, "l", "_ | ⟨x, xs⟩")
        .expect("`rcases l with _ | ⟨x, xs⟩` must map the tuple over List.cons's two fields");

    assert_eq!(state.goals().len(), 2, "List split should leave two goals");
    assert!(
        state.goals()[0].local_ctx.is_empty(),
        "the List.nil branch binds no field, got {:?}",
        state.goals()[0].local_ctx
    );
    let cons_ctx = &state.goals()[1].local_ctx;
    assert_eq!(
        cons_ctx.len(),
        2,
        "the List.cons branch must carry both fields, got {cons_ctx:?}"
    );
    assert_eq!(
        cons_ctx[0].name, "x",
        "the tuple's first component names the HEAD field"
    );
    assert_eq!(
        cons_ctx[1].name, "xs",
        "the tuple's second component names the TAIL field"
    );
}
