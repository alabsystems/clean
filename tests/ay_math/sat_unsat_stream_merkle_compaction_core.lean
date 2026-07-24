-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Compact UNSAT streaming Merkle compaction contract for ay. Propositions stand
-- for proof chunks, retained accepted chains, chunk digests, Merkle summaries,
-- public reports, and missing/evicted/corrupt no-claim diagnostics.

def AyUSMCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSMCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSMCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSMCDigestLink
    (proofChunk : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) :=
  AyUSMCConj
    (AyUSMCMap proofChunk chunkDigest)
    (AyUSMCMap chunkDigest merkleRoot)

def AyUSMCRetainedProofChain
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUSMCConj proofChunk
    (AyUSMCConj acceptedReport
      (AyUSMCConj
        (AyUSMCMap proofChunk emptyClause)
        (AyUSMCConj
          (AyUSMCMap emptyClause visibleUnsat)
          (AyUSMCMap visibleUnsat originalUnsat))))

def AyUSMCMerkleSummary
    (chunkDigest : Prop) (merkleRoot : Prop)
    (summaryRecord : Prop) :=
  AyUSMCConj summaryRecord
    (AyUSMCConj chunkDigest merkleRoot)

def AyUSMCCompactedRetained
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) (summaryRecord : Prop) :=
  AyUSMCConj
    (AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat)
    (AyUSMCConj
      (AyUSMCDigestLink proofChunk chunkDigest merkleRoot)
      (AyUSMCMerkleSummary chunkDigest merkleRoot summaryRecord))

def AyUSMCUnavailableChunk
    (missingChunk : Prop) (evictedChunk : Prop) (corruptChunk : Prop)
    (noClaim : Prop) :=
  AyUSMCConj noClaim
    (AyUSMCDisj missingChunk (AyUSMCDisj evictedChunk corruptChunk))

def AyUSMCPublicReport
    (noClaim : Prop) (originalUnsat : Prop) :=
  AyUSMCDisj noClaim originalUnsat

theorem ay_usmc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSMCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usmc_conj_left
    (p : Prop) (q : Prop) :
    AyUSMCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usmc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSMCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usmc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSMCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usmc_retained_chunk
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat ->
    proofChunk := by
  intro chain
  exact ay_usmc_conj_left proofChunk
    (AyUSMCConj acceptedReport
      (AyUSMCConj
        (proofChunk -> emptyClause)
        (AyUSMCConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat))))
    chain

theorem ay_usmc_retained_accepted
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat ->
    acceptedReport := by
  intro chain
  exact chain acceptedReport
    (fun _chunk tail =>
      tail acceptedReport
        (fun accepted _maps => accepted))

theorem ay_usmc_retained_empty_clause
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat ->
    emptyClause := by
  intro chain
  exact chain emptyClause
    (fun chunk tail =>
      tail emptyClause
        (fun _accepted maps =>
          maps emptyClause
            (fun chunk_to_empty _tail2 => chunk_to_empty chunk)))

theorem ay_usmc_retained_original_unsat
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro chain
  exact chain originalUnsat
    (fun chunk tail =>
      tail originalUnsat
        (fun _accepted maps =>
          maps originalUnsat
            (fun chunk_to_empty tail2 =>
              tail2 originalUnsat
                (fun empty_to_visible visible_to_original =>
                  visible_to_original (empty_to_visible (chunk_to_empty chunk))))))

theorem ay_usmc_digest_chunk
    (proofChunk : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) :
    AyUSMCDigestLink proofChunk chunkDigest merkleRoot ->
    proofChunk ->
    chunkDigest := by
  intro link
  exact link (proofChunk -> chunkDigest)
    (fun chunk_to_digest _digest_to_root => chunk_to_digest)

theorem ay_usmc_digest_root
    (proofChunk : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) :
    AyUSMCDigestLink proofChunk chunkDigest merkleRoot ->
    chunkDigest ->
    merkleRoot := by
  intro link
  exact link (chunkDigest -> merkleRoot)
    (fun _chunk_to_digest digest_to_root => digest_to_root)

theorem ay_usmc_summary_record
    (chunkDigest : Prop) (merkleRoot : Prop)
    (summaryRecord : Prop) :
    AyUSMCMerkleSummary chunkDigest merkleRoot summaryRecord ->
    summaryRecord := by
  intro summary
  exact ay_usmc_conj_left summaryRecord
    (AyUSMCConj chunkDigest merkleRoot)
    summary

theorem ay_usmc_compacted_chain
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) (summaryRecord : Prop) :
    AyUSMCCompactedRetained proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat chunkDigest merkleRoot summaryRecord ->
    AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat := by
  intro compacted
  exact ay_usmc_conj_left
    (AyUSMCRetainedProofChain proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat)
    (AyUSMCConj
      (AyUSMCDigestLink proofChunk chunkDigest merkleRoot)
      (AyUSMCMerkleSummary chunkDigest merkleRoot summaryRecord))
    compacted

theorem ay_usmc_compacted_summary
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) (summaryRecord : Prop) :
    AyUSMCCompactedRetained proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat chunkDigest merkleRoot summaryRecord ->
    AyUSMCMerkleSummary chunkDigest merkleRoot summaryRecord := by
  intro compacted
  exact compacted
    (AyUSMCMerkleSummary chunkDigest merkleRoot summaryRecord)
    (fun _chain tail =>
      tail (AyUSMCMerkleSummary chunkDigest merkleRoot summaryRecord)
        (fun _link summary => summary))

theorem ay_usmc_report_unsat
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUSMCPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_usmc_disj_right noClaim originalUnsat unsat

theorem ay_usmc_report_no_claim
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUSMCPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_usmc_disj_left noClaim originalUnsat no_claim

theorem ay_usmc_compaction_preserves_unsat_soundness
    (proofChunk : Prop) (acceptedReport : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (chunkDigest : Prop)
    (merkleRoot : Prop) (summaryRecord : Prop)
    (noClaim : Prop) :
    AyUSMCCompactedRetained proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat chunkDigest merkleRoot summaryRecord ->
    AyUSMCPublicReport noClaim originalUnsat := by
  intro compacted
  exact ay_usmc_report_unsat noClaim originalUnsat
    (ay_usmc_retained_original_unsat proofChunk acceptedReport emptyClause
      visibleUnsat originalUnsat
      (ay_usmc_compacted_chain proofChunk acceptedReport emptyClause
        visibleUnsat originalUnsat chunkDigest merkleRoot summaryRecord
        compacted))

theorem ay_usmc_unavailable_no_claim
    (missingChunk : Prop) (evictedChunk : Prop) (corruptChunk : Prop)
    (noClaim : Prop) :
    AyUSMCUnavailableChunk missingChunk evictedChunk corruptChunk noClaim ->
    noClaim := by
  intro unavailable
  exact ay_usmc_conj_left noClaim
    (AyUSMCDisj missingChunk (AyUSMCDisj evictedChunk corruptChunk))
    unavailable

theorem ay_usmc_unavailable_report_no_claim
    (missingChunk : Prop) (evictedChunk : Prop) (corruptChunk : Prop)
    (noClaim : Prop) (originalUnsat : Prop) :
    AyUSMCUnavailableChunk missingChunk evictedChunk corruptChunk noClaim ->
    AyUSMCPublicReport noClaim originalUnsat := by
  intro unavailable
  exact ay_usmc_report_no_claim noClaim originalUnsat
    (ay_usmc_unavailable_no_claim
      missingChunk evictedChunk corruptChunk noClaim unavailable)

theorem ay_usmc_missing_cannot_publish_unsat
    (missingChunk : Prop) (evictedChunk : Prop) (corruptChunk : Prop)
    (noClaim : Prop) (originalUnsat : Prop) :
    AyUSMCUnavailableChunk missingChunk evictedChunk corruptChunk noClaim ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro unavailable
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_usmc_unavailable_no_claim
      missingChunk evictedChunk corruptChunk noClaim unavailable)
    unsat
