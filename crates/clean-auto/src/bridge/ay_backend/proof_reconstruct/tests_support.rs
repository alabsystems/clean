// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test fixture helpers for proof-reconstruct direct suites.
//!
//! Consolidates translation-context setup and Bool variable registration
//! that was duplicated across tests/, tests_em_combinator, tests_trace,
//! tests_trace_rooting, and tests_resolution modules.

use super::{ReconstructionContext, VariableMapping};
use ay::Sort;
use ay_core::{TermId, TermStore};
use clean_kernel::{Expr, FVarId};

/// Create a translation-only context backed by the term store.
pub(super) fn translation_context<'a>(
    terms: &'a TermStore,
    map: &'a VariableMapping,
) -> ReconstructionContext<'a> {
    ReconstructionContext::new(terms, map, 0)
}

/// Create a Bool variable in the term store.
pub(super) fn bool_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

/// Register a Bool variable in both the term store and variable mapping.
pub(super) fn register_bool_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    id: u64,
) -> TermId {
    let tid = terms.mk_var(name, Sort::Bool);
    map.register_var(name, Expr::fvar(FVarId::new(id)), Expr::prop());
    tid
}

/// Register a Bool variable with hypothesis registration (for resolution tests).
///
/// Extends `register_bool_var` by also calling `register_hypothesis`, which
/// is needed for resolution proof reconstruction that looks up hypothesis FVars.
pub(super) fn register_bool_hypothesis_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    id: u64,
) -> TermId {
    let tid = register_bool_var(terms, map, name, id);
    map.register_hypothesis(
        name,
        FVarId::new(id),
        Expr::fvar(FVarId::new(id)),
        Expr::prop(),
    );
    tid
}

/// Per defining gate kind, the number of distinct input clauses a bit-blast
/// refutation RESOLVES ON on its way to the empty clause.
///
/// Walks the refutation backward from its final step, following premises, so a
/// clause that merely sits in the CNF (or feeds a derived clause the final
/// derivation never uses) is not counted. The disequality clause has no gate and
/// is not counted. `proof` must already have passed
/// [`BvBlastProof::validate`](ay_proof::bv_blast_export::BvBlastProof::validate),
/// which guarantees dense, in-order clause and step ids.
#[cfg(feature = "ay-bv-blast")]
pub(super) fn refutation_core_gate_kinds(
    proof: &ay_proof::bv_blast_export::BvBlastProof,
) -> std::collections::HashMap<ay_proof::bv_blast_export::BitLemmaKind, usize> {
    use ay_proof::bv_blast_export::ClauseProvenance;

    let n_clauses = proof.clauses.len();
    let steps = &proof.refutation.steps;
    let mut cited = vec![false; n_clauses];
    let mut visited = vec![false; steps.len()];
    let mut pending: Vec<u32> = steps.last().map(|s| s.id).into_iter().collect();
    while let Some(id) = pending.pop() {
        let id = id as usize;
        if id < n_clauses {
            cited[id] = true;
            continue;
        }
        let index = id - n_clauses;
        let step = &steps[index];
        assert_eq!(
            step.id as usize, id,
            "validated step ids are dense and in order"
        );
        if !std::mem::replace(&mut visited[index], true) {
            pending.extend(step.premises);
        }
    }
    let mut kinds = std::collections::HashMap::new();
    for clause in &proof.clauses {
        if let (true, ClauseProvenance::BitLemmaCnf { lemma }) =
            (cited[clause.id as usize], clause.provenance)
        {
            *kinds
                .entry(proof.bit_lemmas[lemma as usize].kind)
                .or_insert(0) += 1;
        }
    }
    kinds
}

/// Fail-closed shape guard for a NON-identity bit-blast positive, run BEFORE any
/// kernel work.
///
/// Asserts, in order, that the refutation (1) is within
/// [`MAX_REFLECTION_STEPS`](super::pcay_bvshift::MAX_REFLECTION_STEPS), so a
/// producer regression fails here in milliseconds instead of inside a long
/// kernel reduction; (2) resolves on at least one clause of every gate kind in
/// `circuit` (see [`refutation_core_gate_kinds`]); and (3) is longer than
/// `2·width + 1` steps, the whole refutation of an obligation whose sides blast
/// to the SAME output bits (the per-bit `XnorEq` derivation plus the
/// disequality). (2) is the load-bearing check: it is what makes the kernel
/// re-check that follows exercise that circuit's clauses. If a producer change
/// ever makes the two sides fuse again, this fails and the obligation must be
/// replaced, not the assertion relaxed.
///
/// Returns the per-kind core counts so the caller can print them.
#[cfg(feature = "ay-bv-blast")]
pub(super) fn assert_refutation_resolves_through(
    proof: &ay_proof::bv_blast_export::BvBlastProof,
    width: u32,
    circuit: &[ay_proof::bv_blast_export::BitLemmaKind],
    label: &str,
) -> std::collections::HashMap<ay_proof::bv_blast_export::BitLemmaKind, usize> {
    use super::pcay_bvshift::MAX_REFLECTION_STEPS;

    let steps = proof.refutation.steps.len();
    assert!(
        steps <= MAX_REFLECTION_STEPS,
        "{label}: {steps} resolution steps is over the always-on trie-reflection cap \
         {MAX_REFLECTION_STEPS}; the producer regressed"
    );
    let core = refutation_core_gate_kinds(proof);
    for kind in circuit {
        assert!(
            core.get(kind).copied().unwrap_or(0) > 0,
            "{label}: the refutation never resolves on a {kind:?} clause (core: {core:?}), so \
             its kernel re-check would not exercise that circuit; replace the obligation"
        );
    }
    let identity_shape = 2 * width as usize + 1;
    assert!(
        steps > identity_shape,
        "{label}: {steps} steps is no longer than the 2*{width}+1 = {identity_shape}-step \
         refutation of an obligation whose sides blast to the same bits"
    );
    core
}
