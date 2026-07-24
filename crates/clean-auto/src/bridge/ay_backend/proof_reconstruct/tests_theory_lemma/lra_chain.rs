// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::boundary::{
    assert_lra_boundary_description_starts_with, assert_lra_trust_boundary,
    lra_boundary_description,
};
use super::support::semantic::{
    mk_real_int_const, register_int_const, register_int_var, register_real_var,
};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, ReconstructionError, TermStore,
    VariableMapping,
};

fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn nat_succ(arg: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        arg.clone(),
    )
}

fn register_int_expr_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    expr: Expr,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, ay::Sort::Int);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var(name, expr, int_ty);
    tid
}

fn register_int_ofnat_ctor_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    nat_expr: Expr,
) -> ay_core::TermId {
    register_int_expr_as_var(
        terms,
        map,
        name,
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_expr,
        ),
    )
}

fn register_int_negsucc_ctor_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    nat_expr: Expr,
) -> ay_core::TermId {
    register_int_expr_as_var(
        terms,
        map,
        name,
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            nat_expr,
        ),
    )
}

#[test]
fn test_theory_lemma_lra_farkas_non_unit_coefficients_fail_semantic_validation() {
    // [2, 1] on 5 ≤ x, x ≤ 3 leaves x unmatched in the Farkas sum. The active
    // subset is malformed and should stop at semantic validation rather than
    // entering chain replay.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_5x = terms.mk_le(five, x);
    let le_x3 = terms.mk_le(x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("malformed non-unit chain should record first_diagnostic");
    let ReconstructionError::TrustBoundary { description, .. } = &diagnostic.error else {
        return;
    };
    assert!(
        description.starts_with("Farkas semantic validation failed:"),
        "malformed non-unit chain should fail semantic validation, got {description:?}"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_int_chain_constructor_form_ofnat_alias_vars_fail_semantic_validation(
) {
    // Constructor-form Lean expressions stored behind ay Vars are boundary-only
    // after active-subset semantic validation. They no longer model native ay
    // constants closely enough to reach Expr-level closeout.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let zero = nat_zero();
    let one = nat_succ(&zero);
    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let one_var = register_int_ofnat_ctor_as_var(&mut terms, &mut map, "const1", one);
    let zero_var = register_int_ofnat_ctor_as_var(&mut terms, &mut map, "const0", zero);

    let le_1x = terms.mk_le(one_var, x);
    let le_x0 = terms.mk_le(x, zero_var);
    let not_le_1x = terms.mk_not(le_1x);
    let not_le_x0 = terms.mk_not(le_x0);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_1x, not_le_x0], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_int_chain_constructor_form_negsucc_alias_vars_fail_semantic_validation(
) {
    // Negative constructor-form Lean expressions stored behind ay Vars belong
    // to the semantic-validation boundary bucket for the same reason as the
    // `Int.ofNat` alias-var fixture above.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let zero = nat_zero();
    let one = nat_succ(&zero);
    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let neg1 = register_int_negsucc_ctor_as_var(&mut terms, &mut map, "constNeg1", zero);
    let neg2 = register_int_negsucc_ctor_as_var(&mut terms, &mut map, "constNeg2", one);

    let le_neg1_x = terms.mk_le(neg1, x);
    let le_x_neg2 = terms.mk_le(x, neg2);
    let not_le_neg1_x = terms.mk_not(le_neg1_x);
    let not_le_x_neg2 = terms.mk_not(le_x_neg2);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_neg1_x, not_le_x_neg2], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_three_le_bounds_chain() {
    // 3 pure Le bounds with unit coefficients that chain: a ≤ b, b ≤ c, c ≤ d.
    // The active sum leaves the outer endpoints unmatched, so semantic
    // validation rejects the certificate before chain replay is attempted.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    // Three chaining Le bounds: a ≤ b, b ≤ c, c ≤ d
    let le_ab = terms.mk_le(a, b);
    let le_bc = terms.mk_le(b, c);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_bc = terms.mk_not(le_bc);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_bc, not_le_cd], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_four_le_bounds_chain() {
    // 4 chaining Le bounds: a ≤ b, b ≤ c, c ≤ d, d ≤ e with cert [1, 1, 1, 1].
    // The active sum still leaves the outer endpoints unmatched, so semantic
    // validation rejects the certificate before chain replay is attempted.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);
    let e = register_int_var(&mut terms, &mut map, "fvar_5", 5);

    let le_ab = terms.mk_le(a, b);
    let le_bc = terms.mk_le(b, c);
    let le_cd = terms.mk_le(c, d);
    let le_de = terms.mk_le(d, e);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_bc = terms.mk_not(le_bc);
    let not_le_cd = terms.mk_not(le_cd);
    let not_le_de = terms.mk_not(le_de);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_le_ab, not_le_bc, not_le_cd, not_le_de],
        farkas,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_two_bound_int_chain_non_eliminating_endpoints_fail_semantic_validation(
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let le_xb = terms.mk_le(x, b);
    let le_by = terms.mk_le(b, y);
    let not_le_xb = terms.mk_not(le_xb);
    let not_le_by = terms.mk_not(le_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xb, not_le_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    let description = lra_boundary_description(&result, 0);
    assert!(
        !description.contains("missing transitivity lemma"),
        "valid Int chains should no longer be classified as missing transitivity lemmas: {description:?}"
    );
    // After #2902, purely symbolic chains where endpoint variables don't
    // eliminate in the Farkas linear combination are caught by the semantic
    // validator before the chain builder runs. The validator message is the
    // correct steady-state for this test fixture.
    assert!(
        description.starts_with("Farkas semantic validation failed:"),
        "symbolic chain with non-eliminating endpoints should fail semantic validation, got {description:?}"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_chain_symbolic_closeout_frontier_reports_exact_boundary() {
    // Honest ay arithmetic terms with native constants make this active subset
    // semantically valid:
    //   (x + 2) ≤ y, y ≤ (x + 1)
    // The remaining failure is the intentional Real symbolic closeout frontier.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let y = register_real_var(&mut terms, &mut map, "fvar_2", 2);
    let two = mk_real_int_const(&mut terms, 2);
    let one = mk_real_int_const(&mut terms, 1);

    let x_plus_2 = terms.mk_add(vec![x, two]);
    let x_plus_1 = terms.mk_add(vec![x, one]);
    let le_xp2_y = terms.mk_le(x_plus_2, y);
    let le_y_xp1 = terms.mk_le(y, x_plus_1);
    let not_le_xp2_y = terms.mk_not(le_xp2_y);
    let not_le_y_xp1 = terms.mk_not(le_y_xp1);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xp2_y, not_le_y_xp1], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    let description = lra_boundary_description(&result, 0);
    assert!(
        description.starts_with("non-cyclic Le chain over Real has no kernel closing proof"),
        "semantically valid Real chain should report the closeout frontier, got {description:?}"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_zero_coefficient_pruned_symbolic_residue_fails_semantic_validation()
{
    // Farkas certificate with a zero coefficient [0, 1] on chaining bounds.
    // After zero-coefficient pruning (#302 W4 2550), bound 0 (5 ≤ x) is
    // dropped, leaving only bound 1 (x ≤ 3). That residue is not a valid
    // conflict by itself, so semantic validation rejects the degenerate
    // certificate [0, 1] before any chain or closeout logic runs.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let three = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_5x = terms.mk_le(five, x);
    let le_x3 = terms.mk_le(x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[0, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_lt_chain_two_bounds() {
    // Two strict inequality bounds: x < b, b < y.
    // The active sum leaves x and y unmatched, so semantic validation rejects
    // the certificate before any Lt-chain replay is attempted.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let lt_xb = terms.mk_lt(x, b);
    let lt_by = terms.mk_lt(b, y);
    let not_lt_xb = terms.mk_not(lt_xb);
    let not_lt_by = terms.mk_not(lt_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_xb, not_lt_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_mixed_le_lt_chain() {
    // Mixed: x ≤ b, b < y.
    // The active sum still leaves the symbolic endpoints unmatched, so
    // semantic validation rejects the certificate before mixed-chain replay.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let le_xb = terms.mk_le(x, b);
    let lt_by = terms.mk_lt(b, y);
    let not_le_xb = terms.mk_not(le_xb);
    let not_lt_by = terms.mk_not(lt_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xb, not_lt_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_mixed_lt_le_chain() {
    // Mixed: x < b, b ≤ y.
    // The active sum still leaves the symbolic endpoints unmatched, so
    // semantic validation rejects the certificate before mixed-chain replay.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let lt_xb = terms.mk_lt(x, b);
    let le_by = terms.mk_le(b, y);
    let not_lt_xb = terms.mk_not(lt_xb);
    let not_le_by = terms.mk_not(le_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_xb, not_le_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

#[test]
fn test_theory_lemma_lra_farkas_three_mixed_chain() {
    // Three bounds: a ≤ b, b < c, c ≤ d → mixed N-bound chain.
    // The active sum leaves the outer endpoints unmatched, so semantic
    // validation rejects the certificate before mixed-chain replay.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let lt_bc = terms.mk_lt(b, c);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_lt_bc = terms.mk_not(lt_bc);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_lt_bc, not_le_cd], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}

// Moved from lra_boundary.rs (#2903): this is a valid 3-bound symbolic chain
// (not a malformed certificate), so it belongs in the chain-focused file.
#[test]
fn test_theory_lemma_lra_farkas_three_bounds_mixed_chain_symbolic() {
    // LRA Farkas with 3 chaining bounds: {¬(a ≤ b), ¬(b < c), ¬(c ≤ d)} with cert [1, 1, 1].
    // The active subset is structurally chain-shaped, but semantic validation
    // rejects it because endpoint variables a and d do not eliminate.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let d = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    let le_ab = terms.mk_le(a, b);
    let lt_bc = terms.mk_lt(b, c);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_lt_bc = terms.mk_not(lt_bc);
    let not_le_cd = terms.mk_not(le_cd);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_lt_bc, not_le_cd], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_lra_boundary_description_starts_with(&result, 0, "Farkas semantic validation failed:");
}
