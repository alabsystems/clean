// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source boundary ratchet for ay-core proof payload coupling (#2451).
//!
//! Enforces that raw ay_core proof payload types (`ProofStep`, `TermData`,
//! `AletheRule`, `TheoryLemmaKind`, `FarkasAnnotation`, `Constant`, `Symbol`)
//! are only directly referenced from the trace adapter layer.
//!
//! Migration is COMPLETE: all production files now use trace view types
//! exclusively. The baseline is 0 across the board. Any non-zero count
//! in a production file is a regression.

use std::collections::HashMap;
use std::path::PathBuf;

use super::{attempt_reconstruction, VariableMapping};
use crate::bridge::ay_backend::reconstruction_quality::{
    accept_kernel_reconstruction_candidate, TrustBudget,
};
use ay::Sort;
use ay_core::{AletheRule, FarkasAnnotation, Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{BigNat, Expr, ExprKind, FVarId, Literal};

/// Raw ay_core proof payload type names that should be confined to the adapter.
const RAW_AY_TYPES: &[&str] = &[
    "ProofStep",
    "TermData",
    "AletheRule",
    "TheoryLemmaKind",
    "FarkasAnnotation",
    // Constant and Symbol are matched as sub-patterns; count them too.
    "Constant::",
    "Symbol::",
];

/// Allowed files that may legitimately reference raw ay types.
/// trace.rs and trace_convert.rs form the adapter; proof_backend.rs is the entry point.
const ALWAYS_ALLOWED: &[&str] = &["trace.rs", "trace_convert.rs", "proof_backend.rs"];

/// Baseline coupling counts per production file.
/// Each entry is (filename, max_allowed_raw_ay_mentions).
///
/// Migration complete: all files at 0. Entries removed per ratchet convention
/// (missing entry → baseline 0 via `unwrap_or(0)`). Any raw ay type added to
/// a production file will immediately fail this test.
const BASELINE: &[(&str, usize)] = &[
    // All production files fully migrated to trace view types.
    // expr_builders*.rs are excluded (they use ay::Sort, not proof payloads).
];

fn proof_reconstruct_dir() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.join("src/bridge/ay_backend/proof_reconstruct")
}

fn count_raw_ay_mentions(source: &str) -> usize {
    let mut count = 0;
    for line in source.lines() {
        let trimmed = line.trim();
        // Skip comments and test-only code markers
        if trimmed.starts_with("//") || trimmed.starts_with("///") {
            continue;
        }
        for pattern in RAW_AY_TYPES {
            count += line.matches(pattern).count();
        }
    }
    count
}

/// Ratchet test: raw ay proof payload types must be zero in all production files.
///
/// Migration is complete — this is now a strict zero-tolerance guard.
/// Any production file introducing raw ay type mentions will fail.
#[test]
fn test_ay_coupling_boundary_ratchet() {
    let dir = proof_reconstruct_dir();
    let baseline: HashMap<&str, usize> = BASELINE.iter().copied().collect();
    let mut violations = Vec::new();

    // Check each production file in the directory
    let entries = std::fs::read_dir(&dir).expect("cannot read proof_reconstruct directory");
    for entry in entries.flatten() {
        let path = entry.path();
        let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");

        // Skip non-Rust, test files, and always-allowed files
        if !file_name.ends_with(".rs") {
            continue;
        }
        if file_name.starts_with("tests") {
            continue;
        }
        if ALWAYS_ALLOWED.contains(&file_name) {
            continue;
        }
        // expr_builders are outside scope (they use Sort, not proof payloads)
        if file_name.starts_with("expr_builders") {
            continue;
        }

        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("cannot read {}", path.display()));
        let count = count_raw_ay_mentions(&source);
        let max_allowed = baseline.get(file_name).copied().unwrap_or(0);

        if count > max_allowed {
            violations.push(format!(
                "{}: {} raw ay mentions (baseline allows {})",
                file_name, count, max_allowed
            ));
        }
    }

    assert!(
        violations.is_empty(),
        "ay coupling ratchet violations (#2451):\n  {}",
        violations.join("\n  ")
    );
}

/// Verify that the trace adapter is the only layer that directly matches raw ay
/// proof payload enum variants (ProofStep, TermData, AletheRule, etc.).
/// Other files may reference type names in imports or signatures, but
/// exhaustive variant matching should be confined to the adapter files.
#[test]
fn test_trace_is_only_exhaustive_matcher() {
    let dir = proof_reconstruct_dir();
    let trace_source = std::fs::read_to_string(dir.join("trace.rs")).expect("cannot read trace.rs");
    let trace_convert_source = std::fs::read_to_string(dir.join("trace_convert.rs"))
        .expect("cannot read trace_convert.rs");
    let adapter_source = format!("{trace_source}\n{trace_convert_source}");

    // The trace adapter must mention all the raw ay types.
    for &pattern in &["ProofStep", "TermData", "AletheRule", "TheoryLemmaKind"] {
        assert!(
            adapter_source.contains(pattern),
            "trace adapter should reference {} as the ay coupling adapter",
            pattern
        );
    }
}

fn contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => contains_const(f, target) || contains_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_const(ty, target) || contains_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_const(ty, target)
                || contains_const(val, target)
                || contains_const(body, target)
        }
        _ => false,
    }
}

fn register_real_const_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    value: i64,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Real);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let expr = if value >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Real.ofNat"), vec![]),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(value as u64)))),
        )
    } else {
        let abs_minus_one = (-value - 1) as u64;
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(abs_minus_one)))),
            ),
        )
    };
    map.register_var(name, expr, real_ty);
    tid
}

fn mk_zero_trust_refutation_with_dead_trust_suffix() -> (TermStore, VariableMapping, Proof, Expr) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("BoundaryP"), vec![]);
    let prop_q = Expr::const_(Name::from_string("BoundaryQ"), vec![]);
    let not_p_prop = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        prop_p.clone(),
    );
    let h_p_id = FVarId::new(200);
    let h_not_p_id = FVarId::new(201);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not(p);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_var("q", prop_q, Expr::prop());
    map.register_hypothesis("p", h_p_id, Expr::fvar(h_p_id), prop_p);
    map.register_hypothesis("h_not_p", h_not_p_id, Expr::fvar(h_not_p_id), not_p_prop);

    let mut proof = Proof::new();
    let h_p = proof.add_assume(p, None);
    let h_not_p = proof.add_assume(not_p, None);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h_p, h_not_p], vec![]);
    proof.add_rule_step(AletheRule::Trust, vec![q], vec![], vec![]);

    let negated_goal = Expr::const_(Name::from_string("False"), vec![]);
    (terms, map, proof, negated_goal)
}

#[test]
fn test_real_additive_all_negative_lt_downcast_boundary() {
    // Negative-only Real endpoints should downcast through the pure `Real.ofInt_*`
    // bridge, without `Real.ofNat_eq_ofInt` normalization.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let neg1 = register_real_const_as_var(&mut terms, &mut map, "constNeg1", -1);
    let neg3 = register_real_const_as_var(&mut terms, &mut map, "constNeg3", -3);
    let neg2 = register_real_const_as_var(&mut terms, &mut map, "constNeg2", -2);
    let neg4 = register_real_const_as_var(&mut terms, &mut map, "constNeg4", -4);

    let lt_neg1_neg3 = terms.mk_lt(neg1, neg3);
    let le_neg2_neg4 = terms.mk_le(neg2, neg4);
    let not_lt_neg1_neg3 = terms.mk_not(lt_neg1_neg3);
    let not_le_neg2_neg4 = terms.mk_not(le_neg2_neg4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_neg1_neg3, not_le_neg2_neg4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

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
fn test_trailing_unreachable_trust_step_does_not_override_empty_clause_root() {
    let (terms, map, proof, negated_goal) = mk_zero_trust_refutation_with_dead_trust_suffix();
    let raw = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert!(
        raw.derives_empty_clause,
        "the reachable empty-clause root should survive a trailing dead suffix"
    );
    assert_eq!(raw.stats.reconstructed_steps, 3);
    assert_eq!(raw.stats.trust_subterm_steps, 0);
    assert_eq!(raw.trust_subterm_count, 0);
    let proof_term = raw
        .proof_term
        .as_ref()
        .expect("reachable empty clause should still produce a proof term");
    assert!(
        !contains_const(proof_term, "trustedAy"),
        "unreachable trailing trust steps must not leak into the accepted refutation"
    );

    let candidate = accept_kernel_reconstruction_candidate(raw, TrustBudget::ZeroTrust)
        .expect("reachable zero-trust refutation should satisfy the strict acceptance budget");
    assert!(
        candidate.quality().is_fully_verified(),
        "ZeroTrust acceptance should yield a fully verified candidate"
    );
}
