// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boundary-only fixture helpers for trust-boundary and semantic-validation
//! failure tests.
//!
//! These helpers create ay *variables* whose Lean expressions are concrete
//! constants (e.g. `Int.ofNat 3`). Under active Farkas semantic validation
//! (#2902), these synthetic ay variables are intentionally *not* semantically
//! equivalent to raw ay constants, so tests using them should expect a
//! trust-boundary result.
//!
//! Only boundary and semantic-boundary test modules should import from here.

use super::super::super::ReconstructionResult;
use super::super::{ReconstructionError, VariableMapping};
use crate::bridge::ay_backend::ResidualTrustSummary;
use ay::Sort;
use ay_core::TermStore;
use clean_kernel::name::Name;
use clean_kernel::{BigNat, Expr, ExprKind, Literal};

pub(in super::super) fn assert_lra_trust_boundary(result: &ReconstructionResult, step_index: u32) {
    assert_eq!(
        result.stats.reconstructed_steps, 0,
        "trust-boundary steps must not count as reconstructed: {:?}",
        result.stats
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "expected exactly one trust-boundary step: {:?}",
        result.stats
    );
    assert_eq!(
        result.stats.arithmetic_boundary_steps, 1,
        "expected exactly one arithmetic-boundary residual source: {:?}",
        result.stats
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 1,
        "trust-boundary steps must still count as trust fallbacks: {:?}",
        result.stats
    );
    // When reconstructed_steps == 0, finish_reconstruction forces proof_term
    // to None (#2986). A proof consisting entirely of trust subterms is
    // vacuous and must not be returned. Residual is empty because there is
    // no final proof to derive trust composition from.
    assert_eq!(result.residual, ResidualTrustSummary::empty());
    assert!(
        result.proof_term.is_none(),
        "total-failure trust-boundary should not produce a proof term (#2986)"
    );
    assert!(
        !result.derives_empty_clause,
        "trust-boundary must not claim to prove contradiction"
    );
    assert!(
        result.trust_subterm_count > 0,
        "trust-boundary stats should still track synthesized trust subterms"
    );
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("trust-boundary result should record first_diagnostic");
    assert_eq!(
        diagnostic.step_index,
        Some(step_index),
        "trust-boundary step index should point at the failing theory lemma"
    );
    assert!(
        matches!(
            &diagnostic.error,
            ReconstructionError::TrustBoundary { subsystem, .. } if subsystem.contains("LRA") || subsystem.contains("lra")
        ),
        "expected LRA trust-boundary diagnostic, got {:?}",
        diagnostic.error
    );
}

pub(in super::super) fn lra_boundary_description(
    result: &ReconstructionResult,
    step_index: u32,
) -> &str {
    assert_lra_trust_boundary(result, step_index);
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("trust-boundary result should record first_diagnostic");
    assert!(
        matches!(&diagnostic.error, ReconstructionError::TrustBoundary { .. }),
        "expected trust-boundary diagnostic, got {:?}",
        diagnostic.error
    );
    let ReconstructionError::TrustBoundary { description, .. } = &diagnostic.error else {
        unreachable!("asserted trust-boundary diagnostic above");
    };
    description
}

pub(in super::super) fn assert_lra_boundary_description_starts_with(
    result: &ReconstructionResult,
    step_index: u32,
    prefix: &str,
) {
    let description = lra_boundary_description(result, step_index);
    assert!(
        description.starts_with(prefix),
        "expected LRA trust-boundary description to start with {prefix:?}, got {description:?}"
    );
}

/// Register an Int-sort ay *variable* whose Lean expression is a concrete
/// `Int.ofNat n`.
///
/// This is a boundary-test helper for raw-constant fixture auditing. Under
/// active Farkas semantic validation (`#2902`), these synthetic ay variables
/// are intentionally *not* semantically equivalent to raw ay constants, so
/// tests that use them as stand-ins for raw-constant replay should expect a
/// trust-boundary result rather than a semantically valid replay.
pub(in super::super) fn register_int_const_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    value: u64,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Int);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let int_ofnat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(value))));
    let expr = Expr::app(int_ofnat, nat_lit);
    map.register_var(name, expr, int_ty);
    tid
}

/// Register a Real-sort ay *variable* whose Lean expression is a concrete
/// `Real.ofNat n` (non-negative) or `Real.ofInt (Int.negSucc k)` (negative).
///
/// Like `register_int_const_as_var`, this helper is boundary-only after
/// `#2902`: it preserves unsimplified ay atoms for trust-boundary fixtures, but
/// it must not be treated as a semantically valid raw-constant encoding for
/// active Farkas replay tests.
pub(in super::super) fn register_real_const_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    value: i64,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Real);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let expr = if value >= 0 {
        let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(value as u64))));
        Expr::app(
            Expr::const_(Name::from_string("Real.ofNat"), vec![]),
            nat_lit,
        )
    } else {
        let abs_minus_one = (-value - 1) as u64;
        let int_expr = Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(abs_minus_one)))),
        );
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            int_expr,
        )
    };
    map.register_var(name, expr, real_ty);
    tid
}

#[cfg(test)]
mod contract_tests {
    use super::super::super::{attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof};
    use super::super::kernel::mk_lra_kernel_env;
    use super::super::kernel::mk_real_lra_kernel_env;
    use super::*;

    fn assert_semantic_validation_boundary(
        result: &ReconstructionResult,
        _env: &clean_kernel::Environment,
        msg: &str,
    ) {
        assert_lra_trust_boundary(result, 0);
        let diagnostic = result
            .stats
            .first_diagnostic
            .as_ref()
            .expect("synthetic-constant fixture should record first_diagnostic");
        assert!(
            matches!(&diagnostic.error, ReconstructionError::TrustBoundary { .. }),
            "expected trust-boundary diagnostic, got {:?}",
            diagnostic.error
        );
        let ReconstructionError::TrustBoundary { description, .. } = &diagnostic.error else {
            unreachable!("asserted trust-boundary diagnostic above");
        };
        assert!(
            description.starts_with("Farkas semantic validation failed:"),
            "{msg}: expected semantic validation failure, got {description:?}"
        );
        // After #2986, proof_term is None when reconstructed_steps == 0,
        // so kernel type-checking of the proof term is no longer applicable.
        assert!(
            result.proof_term.is_none(),
            "{msg}: total-failure trust-boundary should not produce a proof term"
        );
    }

    #[test]
    fn test_register_int_const_as_var_fixtures_hit_semantic_farkas_boundary() {
        let mut terms = TermStore::new();
        let mut map = VariableMapping::new();

        let three = register_int_const_as_var(&mut terms, &mut map, "const3", 3);
        let two = register_int_const_as_var(&mut terms, &mut map, "const2", 2);
        let five = register_int_const_as_var(&mut terms, &mut map, "const5", 5);
        let four = register_int_const_as_var(&mut terms, &mut map, "const4", 4);

        let mut proof = Proof::new();
        proof.add_theory_lemma_with_farkas(
            "LRA",
            {
                let le1 = terms.mk_le(three, two);
                let le2 = terms.mk_le(five, four);
                vec![terms.mk_not(le1), terms.mk_not(le2)]
            },
            FarkasAnnotation::from_ints(&[1, 1]),
        );

        let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
        let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

        assert_semantic_validation_boundary(
            &result,
            &mk_lra_kernel_env(),
            "Int synthetic-constant helper contract",
        );
    }

    #[test]
    fn test_register_real_const_as_var_fixtures_hit_semantic_farkas_boundary() {
        let mut terms = TermStore::new();
        let mut map = VariableMapping::new();

        let three = register_real_const_as_var(&mut terms, &mut map, "const3", 3);
        let neg_one = register_real_const_as_var(&mut terms, &mut map, "constNeg1", -1);
        let neg_two = register_real_const_as_var(&mut terms, &mut map, "constNeg2", -2);
        let zero = register_real_const_as_var(&mut terms, &mut map, "const0", 0);

        let mut proof = Proof::new();
        proof.add_theory_lemma_with_farkas(
            "LRA",
            {
                let le1 = terms.mk_le(three, neg_one);
                let le2 = terms.mk_le(neg_two, zero);
                vec![terms.mk_not(le1), terms.mk_not(le2)]
            },
            FarkasAnnotation::from_ints(&[1, 1]),
        );

        let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
        let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

        assert_semantic_validation_boundary(
            &result,
            &mk_real_lra_kernel_env(),
            "Real synthetic-constant helper contract",
        );
    }

    /// Source-scan ratchet: semantic-success test modules must not import
    /// boundary-only fake-constant helpers.
    #[test]
    fn test_no_semantic_success_modules_import_const_as_var() {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let theory_lemma_dir = std::path::Path::new(manifest_dir)
            .join("src/bridge/ay_backend/proof_reconstruct/tests_theory_lemma");

        // Allowlist: only these files may reference register_*_const_as_var
        let allowed = ["support/boundary.rs", "lra_boundary_semantic_boundary.rs"];

        let mut violations = Vec::new();
        for entry in std::fs::read_dir(&theory_lemma_dir).expect("read tests_theory_lemma dir") {
            let entry = entry.expect("dir entry");
            let path = entry.path();
            if path.extension().is_none_or(|e| e != "rs") {
                continue;
            }
            let rel = path.file_name().unwrap().to_str().unwrap().to_string();
            if allowed.iter().any(|a| a.ends_with(&rel)) {
                continue;
            }
            let contents = std::fs::read_to_string(&path).expect("read file");
            if contents.contains("register_int_const_as_var")
                || contents.contains("register_real_const_as_var")
            {
                violations.push(rel);
            }
        }

        assert!(
            violations.is_empty(),
            "Semantic-success modules must not import boundary-only const_as_var helpers. \
             Violations: {violations:?}. Use register_int_const / mk_raw_le from \
             support::semantic instead."
        );
    }
}
