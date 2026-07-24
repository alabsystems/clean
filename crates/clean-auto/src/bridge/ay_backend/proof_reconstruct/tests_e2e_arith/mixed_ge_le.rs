// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2e tests for raw `>=`/`<`/`>=` chains that normalize to `<=`/`<`/`<=`.

use super::support::*;
use super::*;

#[derive(Clone, Copy)]
enum MixedGeLeTheory {
    LiaGeneric,
    Lra,
}

struct MixedGeLeCaseSpec {
    env: Environment,
    sort: Sort,
    ty: Expr,
    five: Expr,
    three: Expr,
    mk_le: fn(&Expr, &Expr) -> Expr,
    mk_lt: fn(&Expr, &Expr) -> Expr,
    context: &'static str,
    theory: MixedGeLeTheory,
}

fn add_mixed_ge_le_root(
    proof: &mut Proof,
    not_ge_x_5: ay_core::TermId,
    not_lt_xy: ay_core::TermId,
    not_ge_3_y: ay_core::TermId,
    farkas: FarkasAnnotation,
    theory: MixedGeLeTheory,
) -> ay_core::ProofId {
    match theory {
        MixedGeLeTheory::LiaGeneric => proof.add_theory_lemma_with_farkas_and_kind(
            "LIA",
            vec![not_ge_x_5, not_lt_xy, not_ge_3_y],
            farkas,
            TheoryLemmaKind::LiaGeneric,
        ),
        MixedGeLeTheory::Lra => proof.add_theory_lemma_with_farkas(
            "LRA",
            vec![not_ge_x_5, not_lt_xy, not_ge_3_y],
            farkas,
        ),
    }
}

fn mk_mixed_ge_le_chain_case(spec: MixedGeLeCaseSpec) -> ArithmeticE2eCase {
    let MixedGeLeCaseSpec {
        env,
        sort,
        ty,
        five,
        three,
        mk_le,
        mk_lt,
        context,
        theory,
    } = spec;
    let test_x = Expr::const_(Name::from_string("testX"), vec![]);
    let test_y = Expr::const_(Name::from_string("testY"), vec![]);
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let ay_five = terms.mk_var("const5", sort.clone());
    let ay_three = terms.mk_var("const3", sort.clone());
    let ay_x = terms.mk_var("testX", sort.clone());
    let ay_y = terms.mk_var("testY", sort);
    map.register_var("const5", five.clone(), ty.clone());
    map.register_var("const3", three.clone(), ty.clone());
    map.register_var("testX", test_x.clone(), ty.clone());
    map.register_var("testY", test_y.clone(), ty);
    let ge_x_5 = terms.mk_app(
        Symbol::Named(">=".to_string()),
        vec![ay_x, ay_five],
        Sort::Bool,
    );
    let lt_xy = terms.mk_lt(ay_x, ay_y);
    let ge_3_y = terms.mk_app(
        Symbol::Named(">=".to_string()),
        vec![ay_three, ay_y],
        Sort::Bool,
    );
    let not_ge_x_5 = terms.mk_not(ge_x_5);
    let not_lt_xy = terms.mk_not(lt_xy);
    let not_ge_3_y = terms.mk_not(ge_3_y);
    let le_5x_prop = mk_le(&five, &test_x);
    let lt_xy_prop = mk_lt(&test_x, &test_y);
    let le_y3_prop = mk_le(&test_y, &three);
    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    map.register_hypothesis("h_5_le_x", h1_id, Expr::fvar(h1_id), le_5x_prop.clone());
    map.register_hypothesis("h_x_lt_y", h2_id, Expr::fvar(h2_id), lt_xy_prop.clone());
    map.register_hypothesis("h_y_le_3", h3_id, Expr::fvar(h3_id), le_y3_prop.clone());
    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let s0 = add_mixed_ge_le_root(
        &mut proof, not_ge_x_5, not_lt_xy, not_ge_3_y, farkas, theory,
    );
    let s1 = proof.add_assume(ge_x_5, None);
    let s2 = proof.add_resolution(vec![not_lt_xy, not_ge_3_y], not_ge_x_5, s0, s1);
    let s3 = proof.add_assume(lt_xy, None);
    let s4 = proof.add_resolution(vec![not_ge_3_y], not_lt_xy, s2, s3);
    let s5 = proof.add_assume(ge_3_y, None);
    proof.add_resolution(vec![], not_ge_3_y, s4, s5);
    ArithmeticE2eCase {
        env,
        terms,
        map,
        proof,
        neg_goal: negated_false_goal(),
        hyps: vec![
            (h1_id, "h_5_le_x", le_5x_prop),
            (h2_id, "h_x_lt_y", lt_xy_prop),
            (h3_id, "h_y_le_3", le_y3_prop),
        ],
        context,
    }
}

/// Build an e2e case mixing raw `>=` bounds with a regular `<` bound in a
/// 3-step transitivity chain.
///
/// ay terms: `ge(x, 5)`, `lt(x, y)`, `ge(3, y)`
/// After normalization: `5 <= x`, `x < y`, `y <= 3` → contradiction.
///
/// This exercises `>=` → `<=` swapped-arg normalization inside the chain
/// closer path (transitivity), not just the single-bound concrete path
/// tested by `normalization::mk_lra_raw_ge_normalization_case`.
fn mk_lia_mixed_ge_le_chain_case() -> ArithmeticE2eCase {
    mk_mixed_ge_le_chain_case(MixedGeLeCaseSpec {
        env: mk_env_for_int_arith(),
        sort: Sort::Int,
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        five: mk_int_ofnat(5),
        three: mk_int_ofnat(3),
        mk_le: mk_le_int,
        mk_lt: mk_lt_int,
        context: "LIA mixed ge/le chain e2e",
        theory: MixedGeLeTheory::LiaGeneric,
    })
}

fn mk_lra_mixed_ge_le_chain_case() -> ArithmeticE2eCase {
    mk_mixed_ge_le_chain_case(MixedGeLeCaseSpec {
        env: mk_env_for_real_arith(),
        sort: Sort::Real,
        ty: Expr::const_(Name::from_string("Real"), vec![]),
        five: mk_real_ofnat(5),
        three: mk_real_ofnat(3),
        mk_le: mk_le_real,
        mk_lt: mk_lt_real,
        context: "LRA mixed ge/le chain e2e",
        theory: MixedGeLeTheory::Lra,
    })
}

#[test]
fn test_e2e_lia_mixed_ge_le_chain_type_checks() {
    let case = mk_lia_mixed_ge_le_chain_case();
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}

#[test]
fn test_e2e_lra_mixed_ge_le_chain_type_checks() {
    let case = mk_lra_mixed_ge_le_chain_case();
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}
