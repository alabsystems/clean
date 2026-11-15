// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The `drup` step AY prints for a transported resolution chain.
//!
//! Since AY d39838422a (2026-09-30), a resolution chain of 8 or more links is
//! one `drup` step: its premises are the chain's clauses, in AY's order, and its
//! `:args` is the lemma. Carcara's reverse unit propagation used to rescan the
//! premises after every literal it propagated, so such a step cost the square
//! of its premise count, and trust-cg's `BSR_I64` certificate took 150 CPU-s in
//! `clean cert verify-external` (`third-party/carcara/DOWNSTREAM.md`). The
//! linear bound is pinned in the vendored crate (`drup::rup_cost`, which counts
//! the work of both implementations). These tests send the same shape through
//! this adapter: the certificate verifies, and a mutant of its `drup` step is
//! refused at that step.

use super::verify_alethe_proof;

const LINKS: usize = 2_000;

/// `a`, `b` and the chain `a -> x1 -> ... -> x(n-1) -> (not b)`. The proof
/// derives `(cl (not a) (not b))` by one `drup` step over the chain's clauses,
/// listed in a scrambled order (minus the clause at `drop`, if any), and
/// resolves it with `a` and `b`.
fn chain_certificate(n: usize, drop: Option<usize>) -> (String, String) {
    let atom = |i: usize| match i {
        0 => "a".to_owned(),
        i if i == n => "b".to_owned(),
        i => format!("x{i}"),
    };
    let link = |i: usize| {
        let head = if i + 1 == n {
            "(not b)".to_owned()
        } else {
            atom(i + 1)
        };
        format!("(not {}) {head}", atom(i))
    };
    let mut problem =
        String::from("(set-logic QF_UF)\n(declare-const a Bool)\n(declare-const b Bool)\n");
    for i in 1..n {
        problem += &format!("(declare-const x{i} Bool)\n");
    }
    problem += "(assert a)\n(assert b)\n";
    let mut proof = String::from("(assume ha a)\n(assume hb b)\n");
    for i in 0..n {
        problem += &format!("(assert (or {}))\n", link(i));
        proof += &format!("(assume h{i} (or {}))\n", link(i));
        proof += &format!("(step c{i} (cl {}) :rule or :premises (h{i}))\n", link(i));
    }
    let premises: Vec<String> = (0..n)
        .map(|i| (i * 7919) % n)
        .filter(|&i| Some(i) != drop)
        .map(|i| format!("c{i}"))
        .collect();
    proof += &format!(
        "(step lemma (cl (not a) (not b)) :rule drup :premises ({}) :args ((cl (not a) (not b))))\n",
        premises.join(" ")
    );
    proof += "(step end (cl) :rule resolution :premises (lemma ha hb))\n";
    (problem, proof)
}

fn rejected_at_the_drup_step(problem: &str, proof: &str) {
    let error = verify_alethe_proof(problem, proof)
        .expect_err("a drup step whose lemma does not follow must be refused");
    let diagnostic = error.to_string();
    assert!(
        diagnostic.contains("step 'lemma' with rule 'drup'"),
        "expected the refusal at the drup step, got: {diagnostic}"
    );
}

#[test]
fn a_chain_shaped_drup_certificate_verifies() {
    let (problem, proof) = chain_certificate(LINKS, None);
    match verify_alethe_proof(&problem, &proof) {
        Ok(true) => {}
        other => panic!("the chain certificate must verify completely, got {other:?}"),
    }
}

#[test]
fn a_drup_step_missing_one_link_is_refused() {
    for drop in [0, LINKS / 2, LINKS - 1] {
        let (problem, proof) = chain_certificate(LINKS, Some(drop));
        rejected_at_the_drup_step(&problem, &proof);
    }
}

#[test]
fn a_drup_step_with_a_flipped_lemma_literal_is_refused() {
    let (problem, proof) = chain_certificate(LINKS, None);
    let lemma = "(cl (not a) (not b))";
    assert_eq!(proof.matches(lemma).count(), 2);
    rejected_at_the_drup_step(&problem, &proof.replace(lemma, "(cl a (not b))"));
}
