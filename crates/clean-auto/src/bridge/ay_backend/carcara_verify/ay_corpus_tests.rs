// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! AY's real Alethe certificates from trust-cg's resident-session corpus.
//!
//! Every file under `ay_corpus/` was minted by AY 0.26.0 (commit cc347ee0a)
//! with trust-cg's one-shot argv, `ay -smt2 F --strict-proofs --proof P
//! --proof-format alethe`, from the corpus query named in the file (the id is
//! the query's SHA-256 prefix). Files without a suffix are byte-for-byte AY
//! output. `packed_memory_*` and `named_product_*` keep AY's definitions and
//! steps verbatim and close the refutation with one `trans`/`resolution`.
//! `*.completed.alethe` is the only hand-written proof.
//!
//! Clean 8606 (Carcara fecb4224) rejected the first three shapes. It reported
//! `arrays_idx` as an unknown rule and could not normalize bit-vector
//! `poly_simp`. Carcara d62d45cf checks both. These tests pin that the checks
//! are real. Every mutant keeps the certificate consistent, so only the
//! mutated rule can reject it, and the rejection must name that step.
//!
//! The last two shapes are AY defects, and Clean must keep refusing them. One
//! refutation is a single `hole`. The other assumes a term that is not the
//! input assertion.
//!
//! `zext_*` are AY 0.27.0 (commit 4635f0a9b) output, byte for byte, for the
//! two shapes in which AY relies on Clean's Alethe dialect reading
//! `zero_extend` as its definition (`third-party/carcara/DOWNSTREAM.md`
//! § Dialect): a packed-lane `refl` identity (`t1.packed.23/31/38`) and a
//! complete-blast `cong` over a `define-fun` whose body is a `zero_extend`
//! (`t1.cbb3/8/32.cg`). They are 2 of the 8 distinct proof documents behind
//! the 14 trust-cg rows measured for this reading on 2026-09-30: those 14 are
//! six byte-identical pairs plus two, the 8 total 5.8 MB, and these two are the
//! smallest of each shape. The producer side is AY's own conformance set.

use super::verify_alethe_proof;

macro_rules! fixture {
    ($name:literal) => {
        include_str!(concat!("ay_corpus/", $name))
    };
}

const ONE_64: &str = "#b0000000000000000000000000000000000000000000000000000000000000001";
const TWO_64: &str = "#b0000000000000000000000000000000000000000000000000000000000000010";

fn replace_exactly(text: &str, from: &str, to: &str, count: usize) -> String {
    assert_eq!(
        text.matches(from).count(),
        count,
        "mutation anchor must occur exactly {count} time(s): {from}"
    );
    text.replace(from, to)
}

fn verifies(problem: &str, proof: &str) {
    match verify_alethe_proof(problem, proof) {
        Ok(true) => {}
        other => panic!("complete certificate must verify, got {other:?}"),
    }
}

fn rejected_at(problem: &str, proof: &str, step: &str, rule: &str) {
    let error = verify_alethe_proof(problem, proof)
        .expect_err("a certificate for a false inference must be rejected");
    let diagnostic = error.to_string();
    assert!(
        diagnostic.contains(&format!("step '{step}' with rule '{rule}'")),
        "expected rejection at step '{step}' ({rule}), got: {diagnostic}"
    );
}

fn incomplete(problem: &str, proof: &str) {
    match verify_alethe_proof(problem, proof) {
        Ok(false) => {}
        other => panic!("a proof with a hole must be reported incomplete, got {other:?}"),
    }
}

#[test]
fn ay_bitvector_poly_simp_certificates_verify() {
    verifies(
        fixture!("poly_wrap_3eb448bf51b1.smt2"),
        fixture!("poly_wrap_3eb448bf51b1.alethe"),
    );
    verifies(
        fixture!("named_product_1b64a90d0e0e.smt2"),
        fixture!("named_product_1b64a90d0e0e.alethe"),
    );
}

#[test]
fn bitvector_poly_simp_rejects_consistent_certificates_for_satisfiable_variants() {
    // x + (2^64 - 1) = x - 2 is false. The problem becomes satisfiable, and the
    // assumption still matches it.
    let problem = replace_exactly(
        fixture!("poly_wrap_3eb448bf51b1.smt2"),
        "(bvsub sa_v91 (_ bv1 64))",
        "(bvsub sa_v91 (_ bv2 64))",
        1,
    );
    let proof = replace_exactly(
        fixture!("poly_wrap_3eb448bf51b1.alethe"),
        "(bvsub sa_v91 (_ bv1 64))",
        "(bvsub sa_v91 (_ bv2 64))",
        1,
    );
    let proof = replace_exactly(
        &proof,
        &format!("(bvsub sa_v91 {ONE_64})"),
        &format!("(bvsub sa_v91 {TWO_64})"),
        1,
    );
    rejected_at(&problem, &proof, "t1", "poly_simp");

    // The coefficient reaches the step only through a proof definition.
    let problem = replace_exactly(
        fixture!("named_product_1b64a90d0e0e.smt2"),
        "(_ bv1 64)",
        "(_ bv2 64)",
        1,
    );
    let proof = replace_exactly(
        fixture!("named_product_1b64a90d0e0e.alethe"),
        ONE_64,
        TWO_64,
        2,
    );
    rejected_at(&problem, &proof, "t1.cbb2.pr", "poly_simp");
}

fn literal(width: u32, value: u128) -> String {
    format!("#b{:0>width$b}", value, width = width as usize)
}

fn identity(width: u32, left: &str, right: &str) -> (String, String) {
    let problem = format!(
        "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(assert (not (= {left} {right})))\n(check-sat)\n"
    );
    let proof = format!(
        "(assume a (not (= {left} {right})))\n(step s (cl (= {left} {right})) :rule poly_simp)\n(step done (cl) :rule resolution :premises (a s))\n"
    );
    (problem, proof)
}

#[test]
fn bitvector_poly_simp_reduces_modulo_exactly_two_to_the_width() {
    for width in [8u32, 64, 65] {
        let modulus = 1u128 << width;
        let half = 1u128 << (width - 1);
        let one = literal(width, 1);
        let zero = literal(width, 0);
        let decrement = format!("(bvsub x {one})");

        // 2^w - 1 is -1 modulo 2^w.
        let (problem, proof) = identity(
            width,
            &format!("(bvadd {} x)", literal(width, modulus - 1)),
            &decrement,
        );
        verifies(&problem, &proof);

        // 2^(w-1) - 1 is -1 only modulo 2^(w-1).
        let (problem, proof) = identity(
            width,
            &format!("(bvadd {} x)", literal(width, half - 1)),
            &decrement,
        );
        rejected_at(&problem, &proof, "s", "poly_simp");

        // 2^(w-1) * x is zero only for even x.
        let (problem, proof) =
            identity(width, &format!("(bvmul {} x)", literal(width, half)), &zero);
        rejected_at(&problem, &proof, "s", "poly_simp");

        // 2^(w-1) * (x + x) = 2^w * x is zero.
        let (problem, proof) = identity(
            width,
            &zero,
            &format!("(bvmul {} (bvadd x x))", literal(width, half)),
        );
        verifies(&problem, &proof);
    }
}

/// PINNED GAP (Carcara d62d45cf, still present on upstream main 126c533141):
/// `Polynomial::modulo` reduces each coefficient but never removes one that
/// becomes zero. When that monomial is on the LEFT of the equality, the
/// leftover zero entry makes `is_zero` fail. A valid identity is then refused
/// in one orientation and accepted in the other. This is incomplete, not
/// unsound: acceptance still requires equal residues. When this starts to
/// verify, delete the `expect_err` half.
#[test]
fn pinned_gap_poly_simp_refuses_a_coefficient_that_vanishes_on_the_left() {
    for width in [8u32, 64] {
        let product = format!(
            "(bvmul {} (bvadd x x))",
            literal(width, 1u128 << (width - 1))
        );
        let zero = literal(width, 0);
        let (problem, proof) = identity(width, &product, &zero);
        rejected_at(&problem, &proof, "s", "poly_simp");
        // Target: the same identity already verifies with its sides swapped.
        let (problem, proof) = identity(width, &zero, &product);
        verifies(&problem, &proof);
    }
}

#[test]
fn ay_packed_memory_array_derivation_verifies() {
    verifies(
        fixture!("packed_memory_592bf7524cd7.smt2"),
        fixture!("packed_memory_592bf7524cd7.alethe"),
    );
}

#[test]
fn packed_memory_mutants_are_rejected_at_the_mutated_step() {
    let problem = fixture!("packed_memory_592bf7524cd7.smt2");
    let proof = fixture!("packed_memory_592bf7524cd7.alethe");
    let low = "((_ extract 7 0) mem_stval_v40_w8)";
    let high = "((_ extract 15 8) mem_stval_v40_w8)";

    // arrays_idx: a read at the written index returns the written value, not
    // another byte. The problem compares against that byte too.
    let assertion_tail = |byte: &str| format!(" mem_base_v9) {byte})))");
    let wrong_problem = replace_exactly(problem, &assertion_tail(low), &assertion_tail(high), 1);
    let mut wrong_proof = replace_exactly(proof, &assertion_tail(low), &assertion_tail(high), 1);
    for step in [
        "t1.packed.31 (cl (= __ay_packed_1_0!28",
        "t2 (cl (= __ay_packed_1_0!49",
    ] {
        wrong_proof = replace_exactly(
            &wrong_proof,
            &format!("(step {step} {low}))"),
            &format!("(step {step} {high}))"),
            1,
        );
    }
    rejected_at(&wrong_problem, &wrong_proof, "t1.packed.31", "arrays_idx");

    // arrays_row: the outer write now hits the read index. Its premise
    // separates a DIFFERENT pair of indices.
    let wrong_problem = replace_exactly(
        problem,
        &format!("(bvadd mem_base_v9 (_ bv1 64)) {high})"),
        &format!("mem_base_v9 {high})"),
        1,
    );
    let wrong_proof = replace_exactly(
        proof,
        &format!("(bvadd mem_base_v9 {ONE_64}) {high})"),
        &format!("mem_base_v9 {high})"),
        2,
    );
    rejected_at(&wrong_problem, &wrong_proof, "t1.packed.50", "arrays_row");

    // arrays_row without its index-disequality premise, or with an unrelated one.
    let premise = ":rule arrays_row :premises (t1.packed.48)";
    for replacement in [
        ":rule arrays_row",
        ":rule arrays_row :premises (t1.packed.35)",
    ] {
        let wrong_proof = replace_exactly(proof, premise, replacement, 1);
        rejected_at(problem, &wrong_proof, "t1.packed.50", "arrays_row");
    }

    // poly_simp inside the index-disequality derivation: (i + 1) - i is not 2.
    let wrong_proof = replace_exactly(
        proof,
        "(_ bv1 64))) :rule poly_simp)",
        "(_ bv2 64))) :rule poly_simp)",
        1,
    );
    rejected_at(problem, &wrong_proof, "t1.packed.34", "poly_simp");

    // Declaring the array step a hole is never a complete proof.
    incomplete(
        problem,
        &replace_exactly(proof, ":rule arrays_idx)", ":rule hole)", 1),
    );
}

#[test]
fn ay_whole_refutation_hole_is_incomplete_and_its_checked_completion_verifies() {
    let problem = fixture!("hole_758d3c8d8705.smt2");
    incomplete(problem, fixture!("hole_758d3c8d8705.alethe"));
    // The completion uses only standard rules: refl, poly_simp, cong and
    // resolution. It is the derivation AY's strict lane should emit here.
    let completed = fixture!("hole_758d3c8d8705.completed.alethe");
    verifies(problem, completed);
    // The completion is checked, not trusted: break its arithmetic premise.
    let broken = replace_exactly(
        completed,
        "(step t2 (cl (= (bvadd (bvmul #b0000000000000000000000000000000000000000000000000000000000001000 (bvadd #b1111111111111111111111111111111111111111111111111111111111111111 sa_v91)) sa_v90)",
        "(step t2 (cl (= (bvadd (bvmul #b0000000000000000000000000000000000000000000000000000000000001000 (bvadd #b1111111111111111111111111111111111111111111111111111111111111110 sa_v91)) sa_v90)",
        1,
    );
    rejected_at(problem, &broken, "t2", "poly_simp");
}

#[test]
fn an_assumption_that_is_not_the_input_assertion_is_rejected() {
    let problem = fixture!("assume_2fedfcfe4439.smt2");
    // AY assumes (not (= (= P true) true)) where the problem asserts
    // (not (= P true)).
    rejected_at(
        problem,
        fixture!("assume_2fedfcfe4439.alethe"),
        "t0",
        "assume",
    );
    // Assuming the asserted term only exposes the next defect: a single hole.
    let assumed_verbatim = replace_exactly(
        fixture!("assume_2fedfcfe4439.alethe"),
        "(not (= (= (bvult bridge_dom_bce_idx (_ bv1024 64)) true) true))",
        "(not (= (bvult bridge_dom_bce_idx (_ bv1024 64)) true))",
        2,
    );
    incomplete(problem, &assumed_verbatim);
}

/// The packed `refl` and the complete-blast `cong` that rely on the dialect's
/// `zero_extend` reading verify; a wrong identity, or a definition that is not
/// a `zero_extend`, is refused at that step; and without the dialect the
/// unmodified rows are refused at the same step, so the dialect is what
/// admits them.
#[test]
fn ay_zero_extend_certificates_verify_only_through_the_dialect_reading() {
    let packed = (
        fixture!("zext_packed_2d494502324b.smt2"),
        fixture!("zext_packed_2d494502324b.alethe"),
    );
    let blast = (
        fixture!("zext_blast_7ca8a6627cf4.smt2"),
        fixture!("zext_blast_7ca8a6627cf4.alethe"),
    );
    verifies(packed.0, packed.1);
    verifies(blast.0, blast.1);

    let identity = "(step t1.packed.23 (cl (= ((_ zero_extend 16) (bvand narrow_a narrow_b)) \
                    (concat (_ bv0 16) (bvand narrow_a narrow_b)))) :rule refl)";
    for wrong in [
        "(step t1.packed.23 (cl (= ((_ zero_extend 16) (bvand narrow_a narrow_b)) \
         (concat (_ bv1 16) (bvand narrow_a narrow_b)))) :rule refl)",
        "(step t1.packed.23 (cl (= ((_ zero_extend 16) (bvand narrow_a narrow_b)) \
         (concat (bvand narrow_a narrow_b) (_ bv0 16)))) :rule refl)",
        "(step t1.packed.23 (cl (= ((_ sign_extend 16) (bvand narrow_a narrow_b)) \
         (concat (_ bv0 16) (bvand narrow_a narrow_b)))) :rule refl)",
    ] {
        let proof = replace_exactly(packed.1, identity, wrong, 1);
        rejected_at(packed.0, &proof, "t1.packed.23", "refl");
    }
    let definition = "(define-fun @ay_cbb_t1_0_w2 () (_ BitVec 32) ((_ zero_extend 24) narrow_b))";
    let proof = replace_exactly(
        blast.1,
        definition,
        &definition.replace("zero_extend", "sign_extend"),
        1,
    );
    rejected_at(blast.0, &proof, "t1.cbb3.cg", "cong");

    for ((problem, proof), step, rule) in [
        (packed, "t1.packed.23", "refl"),
        (blast, "t1.cbb3.cg", "cong"),
    ] {
        let problem = super::bv_literals::normalize(problem).expect("problem literals");
        let proof = super::bv_literals::normalize(proof).expect("proof literals");
        let error =
            super::pb_widths::check_with_parser(&problem, &proof, carcara::parser::Config::new())
                .expect_err("without the dialect a zero_extend identity is not checkable");
        let diagnostic = error.to_string();
        assert!(
            diagnostic.contains(&format!("step '{step}' with rule '{rule}'")),
            "expected the refusal at {step} ({rule}), got: {diagnostic}"
        );
    }
}
