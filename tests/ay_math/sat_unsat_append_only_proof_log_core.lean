-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded append-only UNSAT proof-log soundness for ay. Propositions stand for
-- incremental proof logs, append-only order, prefix digest agreement,
-- dependency coverage, empty-clause witnesses, original reconstruction, and
-- no-claim/recompute diagnostics for truncation, mutation, or suffix mismatch.

def AyUAOPConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUAOPDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUAOPMap (source : Prop) (target : Prop) :=
  source -> target

def AyUAOPAppendOrder
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop) :=
  AyUAOPConj
    (AyUAOPConj prefixLog suffixLog)
    fullLog

def AyUAOPPrefixDigest
    (prefixLog : Prop) (prefixDigest : Prop) (digestAccepted : Prop) :=
  AyUAOPConj
    (AyUAOPMap prefixLog prefixDigest)
    (AyUAOPMap prefixDigest digestAccepted)

def AyUAOPDependencyCoverage
    (fullLog : Prop) (dependencyCoverage : Prop) (emptyClause : Prop) :=
  AyUAOPConj
    (AyUAOPMap fullLog dependencyCoverage)
    (AyUAOPMap dependencyCoverage emptyClause)

def AyUAOPReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUAOPConj
    (AyUAOPMap emptyClause visibleUnsat)
    (AyUAOPMap visibleUnsat originalUnsat)

def AyUAOPAppendOnlyProofLog
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUAOPConj
    (AyUAOPAppendOrder prefixLog suffixLog fullLog)
    (AyUAOPConj
      (AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted)
      (AyUAOPConj
        (AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause)
        (AyUAOPReconstruction emptyClause visibleUnsat originalUnsat)))

def AyUAOPInvalidReuse
    (truncatedLog : Prop) (mutatedLog : Prop) (suffixMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUAOPConj
    (AyUAOPConj noClaim recompute)
    (AyUAOPDisj truncatedLog
      (AyUAOPDisj mutatedLog suffixMismatch))

def AyUAOPPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUAOPDisj noClaim originalUnsat

theorem ay_uaop_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUAOPConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uaop_conj_left
    (p : Prop) (q : Prop) :
    AyUAOPConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uaop_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUAOPDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uaop_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUAOPDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uaop_append_prefix
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop) :
    AyUAOPAppendOrder prefixLog suffixLog fullLog ->
    prefixLog := by
  intro append_order
  have head : AyUAOPConj prefixLog suffixLog :=
    ay_uaop_conj_left (AyUAOPConj prefixLog suffixLog) fullLog
      append_order
  exact ay_uaop_conj_left prefixLog suffixLog head

theorem ay_uaop_append_suffix
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop) :
    AyUAOPAppendOrder prefixLog suffixLog fullLog ->
    suffixLog := by
  intro append_order
  exact append_order suffixLog
    (fun head _full =>
      head suffixLog
        (fun _prefix suffix => suffix))

theorem ay_uaop_append_full_log
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop) :
    AyUAOPAppendOrder prefixLog suffixLog fullLog ->
    fullLog := by
  intro append_order
  exact append_order fullLog
    (fun _head full => full)

theorem ay_uaop_prefix_digest_value
    (prefixLog : Prop) (prefixDigest : Prop) (digestAccepted : Prop) :
    AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted ->
    prefixLog ->
    prefixDigest := by
  intro digest
  exact digest (prefixLog -> prefixDigest)
    (fun prefix_to_digest _digest_to_accept => prefix_to_digest)

theorem ay_uaop_prefix_digest_accepted
    (prefixLog : Prop) (prefixDigest : Prop) (digestAccepted : Prop) :
    AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted ->
    prefixDigest ->
    digestAccepted := by
  intro digest
  exact digest (prefixDigest -> digestAccepted)
    (fun _prefix_to_digest digest_to_accept => digest_to_accept)

theorem ay_uaop_dependency_coverage
    (fullLog : Prop) (dependencyCoverage : Prop) (emptyClause : Prop) :
    AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause ->
    fullLog ->
    dependencyCoverage := by
  intro coverage
  exact coverage (fullLog -> dependencyCoverage)
    (fun full_to_coverage _coverage_to_empty => full_to_coverage)

theorem ay_uaop_dependency_empty_clause
    (fullLog : Prop) (dependencyCoverage : Prop) (emptyClause : Prop) :
    AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _full_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_uaop_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uaop_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uaop_proof_append_order
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUAOPAppendOrder prefixLog suffixLog fullLog := by
  intro proof
  exact ay_uaop_conj_left
    (AyUAOPAppendOrder prefixLog suffixLog fullLog)
    (AyUAOPConj
      (AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted)
      (AyUAOPConj
        (AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause)
        (AyUAOPReconstruction emptyClause visibleUnsat originalUnsat)))
    proof

theorem ay_uaop_proof_digest
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted := by
  intro proof
  exact proof (AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted)
    (fun _append_order tail =>
      tail (AyUAOPPrefixDigest prefixLog prefixDigest digestAccepted)
        (fun digest _rest => digest))

theorem ay_uaop_proof_coverage
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause := by
  intro proof
  exact proof (AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause)
    (fun _append_order tail =>
      tail (AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause)
        (fun _digest rest =>
          rest (AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause)
            (fun coverage _reconstruction => coverage)))

theorem ay_uaop_proof_reconstruction
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUAOPReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUAOPReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _append_order tail =>
      tail (AyUAOPReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _digest rest =>
          rest (AyUAOPReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage reconstruction => reconstruction)))

theorem ay_uaop_proof_full_log
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    fullLog := by
  intro proof
  exact ay_uaop_append_full_log prefixLog suffixLog fullLog
    (ay_uaop_proof_append_order prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat originalUnsat
      proof)

theorem ay_uaop_proof_digest_accepted
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    digestAccepted := by
  intro proof
  exact proof digestAccepted
    (fun append_order tail =>
      tail digestAccepted
        (fun digest _rest =>
          digest digestAccepted
            (fun prefix_to_digest digest_to_accept =>
              digest_to_accept
                (prefix_to_digest
                  (ay_uaop_append_prefix prefixLog suffixLog fullLog
                    append_order)))))

theorem ay_uaop_proof_empty_clause
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro proof
  have full_log : fullLog :=
    ay_uaop_proof_full_log prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat originalUnsat
      proof
  have coverage :
      AyUAOPDependencyCoverage fullLog dependencyCoverage emptyClause :=
    ay_uaop_proof_coverage prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat originalUnsat
      proof
  have covered : dependencyCoverage :=
    ay_uaop_dependency_coverage fullLog dependencyCoverage emptyClause
      coverage full_log
  exact ay_uaop_dependency_empty_clause fullLog dependencyCoverage
    emptyClause coverage covered

theorem ay_uaop_append_only_original_unsat
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro proof
  have empty : emptyClause :=
    ay_uaop_proof_empty_clause prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat originalUnsat
      proof
  have reconstruction :
      AyUAOPReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_uaop_proof_reconstruction prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat originalUnsat
      proof
  have visible : visibleUnsat :=
    ay_uaop_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_uaop_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_uaop_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUAOPPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uaop_disj_right noClaim originalUnsat unsat

theorem ay_uaop_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUAOPPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uaop_disj_left noClaim originalUnsat no_claim

theorem ay_uaop_append_only_publish_sound
    (prefixLog : Prop) (suffixLog : Prop) (fullLog : Prop)
    (prefixDigest : Prop) (digestAccepted : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUAOPAppendOnlyProofLog prefixLog suffixLog fullLog prefixDigest
      digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUAOPPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_uaop_public_unsat_report noClaim originalUnsat
    (ay_uaop_append_only_original_unsat prefixLog suffixLog fullLog
      prefixDigest digestAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof)

theorem ay_uaop_invalid_no_claim
    (truncatedLog : Prop) (mutatedLog : Prop) (suffixMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUAOPInvalidReuse truncatedLog mutatedLog suffixMismatch
      noClaim recompute ->
    noClaim := by
  intro invalid
  exact invalid noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uaop_invalid_recompute
    (truncatedLog : Prop) (mutatedLog : Prop) (suffixMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUAOPInvalidReuse truncatedLog mutatedLog suffixMismatch
      noClaim recompute ->
    recompute := by
  intro invalid
  exact invalid recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uaop_invalid_public_no_claim
    (truncatedLog : Prop) (mutatedLog : Prop) (suffixMismatch : Prop)
    (noClaim : Prop) (originalUnsat : Prop) (recompute : Prop) :
    AyUAOPInvalidReuse truncatedLog mutatedLog suffixMismatch
      noClaim recompute ->
    AyUAOPPublicReport noClaim originalUnsat := by
  intro invalid
  exact ay_uaop_public_no_claim_report noClaim originalUnsat
    (ay_uaop_invalid_no_claim truncatedLog mutatedLog suffixMismatch
      noClaim recompute invalid)

theorem ay_uaop_invalid_cannot_publish_unsat
    (truncatedLog : Prop) (mutatedLog : Prop) (suffixMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUAOPInvalidReuse truncatedLog mutatedLog suffixMismatch
      noClaim recompute ->
    AyUAOPConj noClaim recompute := by
  intro invalid
  exact invalid (AyUAOPConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)
