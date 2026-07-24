-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded digest-rollup soundness for ay UNSAT proof checking. Propositions
-- stand for ordered proof chunks, chunk digest rollups, checkpoint chains,
-- dependency coverage, empty-clause witnesses, original reconstruction, and
-- no-claim/recompute diagnostics for rollup mismatch.

def AyUPDRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPDRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPDRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPDRChunkRollup
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) :=
  AyUPDRConj orderedChunks
    (AyUPDRConj
      (AyUPDRMap orderedChunks chunkDigests)
      (AyUPDRMap chunkDigests publicRoot))

def AyUPDRCheckpointChain
    (chunkDigests : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) :=
  AyUPDRConj
    (AyUPDRMap chunkDigests checkpointChain)
    (AyUPDRMap checkpointChain rootAccepted)

def AyUPDRReplayCoverage
    (orderedChunks : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUPDRConj
    (AyUPDRMap orderedChunks dependencyCoverage)
    (AyUPDRMap dependencyCoverage emptyClause)

def AyUPDRReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPDRConj
    (AyUPDRMap emptyClause visibleUnsat)
    (AyUPDRMap visibleUnsat originalUnsat)

def AyUPDRDigestRollupProof
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPDRConj
    (AyUPDRChunkRollup orderedChunks chunkDigests publicRoot)
    (AyUPDRConj
      (AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted)
      (AyUPDRConj
        (AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause)
        (AyUPDRReconstruction emptyClause visibleUnsat originalUnsat)))

def AyUPDRRollupMismatch
    (chunkOrderMismatch : Prop) (digestMismatch : Prop)
    (checkpointMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUPDRConj
    (AyUPDRConj noClaim recompute)
    (AyUPDRDisj chunkOrderMismatch
      (AyUPDRDisj digestMismatch checkpointMismatch))

def AyUPDRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPDRDisj noClaim originalUnsat

theorem ay_updr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPDRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_updr_conj_left
    (p : Prop) (q : Prop) :
    AyUPDRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_updr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPDRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_updr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPDRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_updr_rollup_ordered_chunks
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) :
    AyUPDRChunkRollup orderedChunks chunkDigests publicRoot ->
    orderedChunks := by
  intro rollup
  exact ay_updr_conj_left orderedChunks
    (AyUPDRConj
      (AyUPDRMap orderedChunks chunkDigests)
      (AyUPDRMap chunkDigests publicRoot))
    rollup

theorem ay_updr_rollup_chunk_digests
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) :
    AyUPDRChunkRollup orderedChunks chunkDigests publicRoot ->
    chunkDigests := by
  intro rollup
  exact rollup chunkDigests
    (fun ordered tail =>
      tail chunkDigests
        (fun ordered_to_digest _digest_to_root =>
          ordered_to_digest ordered))

theorem ay_updr_rollup_public_root
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) :
    AyUPDRChunkRollup orderedChunks chunkDigests publicRoot ->
    publicRoot := by
  intro rollup
  exact rollup publicRoot
    (fun ordered tail =>
      tail publicRoot
        (fun ordered_to_digest digest_to_root =>
          digest_to_root (ordered_to_digest ordered)))

theorem ay_updr_checkpoint_chain_value
    (chunkDigests : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) :
    AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted ->
    chunkDigests ->
    checkpointChain := by
  intro chain
  exact chain (chunkDigests -> checkpointChain)
    (fun digest_to_chain _chain_to_accept => digest_to_chain)

theorem ay_updr_checkpoint_root_accepted
    (chunkDigests : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) :
    AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted ->
    checkpointChain ->
    rootAccepted := by
  intro chain
  exact chain (checkpointChain -> rootAccepted)
    (fun _digest_to_chain chain_to_accept => chain_to_accept)

theorem ay_updr_dependency_coverage
    (orderedChunks : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause ->
    orderedChunks ->
    dependencyCoverage := by
  intro coverage
  exact coverage (orderedChunks -> dependencyCoverage)
    (fun chunks_to_coverage _coverage_to_empty => chunks_to_coverage)

theorem ay_updr_dependency_empty_clause
    (orderedChunks : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _chunks_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_updr_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_updr_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_updr_proof_rollup
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    AyUPDRChunkRollup orderedChunks chunkDigests publicRoot := by
  intro proof
  exact ay_updr_conj_left
    (AyUPDRChunkRollup orderedChunks chunkDigests publicRoot)
    (AyUPDRConj
      (AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted)
      (AyUPDRConj
        (AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause)
        (AyUPDRReconstruction emptyClause visibleUnsat originalUnsat)))
    proof

theorem ay_updr_proof_checkpoint_chain
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted := by
  intro proof
  exact proof (AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted)
    (fun _rollup tail =>
      tail (AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted)
        (fun chain _rest => chain))

theorem ay_updr_proof_coverage
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause := by
  intro proof
  exact proof (AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause)
    (fun _rollup tail =>
      tail (AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause)
        (fun _chain rest =>
          rest (AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause)
            (fun coverage _reconstruction => coverage)))

theorem ay_updr_proof_reconstruction
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    AyUPDRReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUPDRReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _rollup tail =>
      tail (AyUPDRReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _chain rest =>
          rest (AyUPDRReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage reconstruction => reconstruction)))

theorem ay_updr_proof_root_accepted
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    rootAccepted := by
  intro proof
  have rollup :
      AyUPDRChunkRollup orderedChunks chunkDigests publicRoot :=
    ay_updr_proof_rollup orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof
  have chain :
      AyUPDRCheckpointChain chunkDigests checkpointChain rootAccepted :=
    ay_updr_proof_checkpoint_chain orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof
  have digests : chunkDigests :=
    ay_updr_rollup_chunk_digests orderedChunks chunkDigests publicRoot
      rollup
  have checkpoints : checkpointChain :=
    ay_updr_checkpoint_chain_value chunkDigests checkpointChain rootAccepted
      chain digests
  exact ay_updr_checkpoint_root_accepted chunkDigests checkpointChain
    rootAccepted chain checkpoints

theorem ay_updr_proof_empty_clause
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    emptyClause := by
  intro proof
  have rollup :
      AyUPDRChunkRollup orderedChunks chunkDigests publicRoot :=
    ay_updr_proof_rollup orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof
  have coverage :
      AyUPDRReplayCoverage orderedChunks dependencyCoverage emptyClause :=
    ay_updr_proof_coverage orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof
  have ordered : orderedChunks :=
    ay_updr_rollup_ordered_chunks orderedChunks chunkDigests publicRoot
      rollup
  have covered : dependencyCoverage :=
    ay_updr_dependency_coverage orderedChunks dependencyCoverage
      emptyClause coverage ordered
  exact ay_updr_dependency_empty_clause orderedChunks dependencyCoverage
    emptyClause coverage covered

theorem ay_updr_digest_rollup_original_unsat
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  have empty : emptyClause :=
    ay_updr_proof_empty_clause orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof
  have reconstruction :
      AyUPDRReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_updr_proof_reconstruction orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof
  have visible : visibleUnsat :=
    ay_updr_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_updr_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_updr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPDRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_updr_disj_right noClaim originalUnsat unsat

theorem ay_updr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPDRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_updr_disj_left noClaim originalUnsat no_claim

theorem ay_updr_digest_rollup_publish_sound
    (orderedChunks : Prop) (chunkDigests : Prop)
    (publicRoot : Prop) (checkpointChain : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUPDRDigestRollupProof orderedChunks chunkDigests publicRoot
      checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat ->
    AyUPDRPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_updr_public_unsat_report noClaim originalUnsat
    (ay_updr_digest_rollup_original_unsat orderedChunks chunkDigests
      publicRoot checkpointChain rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat proof)

theorem ay_updr_mismatch_no_claim
    (chunkOrderMismatch : Prop) (digestMismatch : Prop)
    (checkpointMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPDRRollupMismatch chunkOrderMismatch digestMismatch
      checkpointMismatch noClaim recompute ->
    noClaim := by
  intro mismatch
  exact mismatch noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_updr_mismatch_recompute
    (chunkOrderMismatch : Prop) (digestMismatch : Prop)
    (checkpointMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPDRRollupMismatch chunkOrderMismatch digestMismatch
      checkpointMismatch noClaim recompute ->
    recompute := by
  intro mismatch
  exact mismatch recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_updr_mismatch_public_no_claim
    (chunkOrderMismatch : Prop) (digestMismatch : Prop)
    (checkpointMismatch : Prop) (noClaim : Prop)
    (originalUnsat : Prop) (recompute : Prop) :
    AyUPDRRollupMismatch chunkOrderMismatch digestMismatch
      checkpointMismatch noClaim recompute ->
    AyUPDRPublicReport noClaim originalUnsat := by
  intro mismatch
  exact ay_updr_public_no_claim_report noClaim originalUnsat
    (ay_updr_mismatch_no_claim chunkOrderMismatch digestMismatch
      checkpointMismatch noClaim recompute mismatch)

theorem ay_updr_mismatch_cannot_publish_unsat
    (chunkOrderMismatch : Prop) (digestMismatch : Prop)
    (checkpointMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPDRRollupMismatch chunkOrderMismatch digestMismatch
      checkpointMismatch noClaim recompute ->
    AyUPDRConj noClaim recompute := by
  intro mismatch
  exact mismatch (AyUPDRConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

