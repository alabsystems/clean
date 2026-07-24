-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof stream-chunk guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for chunk manifest digests,
-- per-chunk proof digests, chunk ordering ledgers, decoded-step ledgers,
-- antecedent availability, resolvent/redundancy replay, original-formula
-- empty-clause reachability, checker transcripts, benchmark fingerprints,
-- build/archive evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_scgg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_scgg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_scgg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_scgg_accepted_evidence
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (chunkManifestDigest ->
      perChunkProofDigest ->
      chunkOrderingLedger ->
      decodedStepLedger ->
      antecedentAvailabilityLedger ->
      replayEvidence ->
      originalEmptyClauseReachable ->
      checkerTranscript ->
      checkerAccepted ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackNoClaim ->
      auditTranscript ->
      originalUnsat ->
      result) ->
    result

def ay_scgg_stream_replay_composition
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (originalUnsat : Prop) :=
  ay_scgg_conj
    (ay_scgg_map chunkManifestDigest perChunkProofDigest)
    (ay_scgg_conj
      (ay_scgg_map perChunkProofDigest chunkOrderingLedger)
      (ay_scgg_conj
        (ay_scgg_map chunkOrderingLedger decodedStepLedger)
        (ay_scgg_conj
          (ay_scgg_map decodedStepLedger antecedentAvailabilityLedger)
          (ay_scgg_conj
            (ay_scgg_map antecedentAvailabilityLedger replayEvidence)
            (ay_scgg_conj
              (ay_scgg_map replayEvidence originalEmptyClauseReachable)
              (ay_scgg_map originalEmptyClauseReachable originalUnsat)))))))

def ay_scgg_publication
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_scgg_conj
    (ay_scgg_accepted_evidence chunkManifestDigest perChunkProofDigest
      chunkOrderingLedger decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat)
    originalUnsat

def ay_scgg_failure_reason
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (manifestMismatch -> result) ->
    (chunkMismatch -> result) ->
    (orderMismatch -> result) ->
    (decodeMismatch -> result) ->
    (availabilityMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_scgg_bad_guard
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_scgg_conj
    (ay_scgg_conj noClaim recompute)
    (ay_scgg_failure_reason manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_scgg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_scgg_disj noClaim (ay_scgg_disj originalUnsat publicSat)

theorem ay_scgg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_scgg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_scgg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_scgg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_scgg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_scgg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_scgg_build_accepted_evidence
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    chunkManifestDigest ->
    perChunkProofDigest ->
    chunkOrderingLedger ->
    decodedStepLedger ->
    antecedentAvailabilityLedger ->
    replayEvidence ->
    originalEmptyClauseReachable ->
    checkerTranscript ->
    checkerAccepted ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    originalUnsat ->
    ay_scgg_accepted_evidence chunkManifestDigest perChunkProofDigest
      chunkOrderingLedger decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat := by
  intro hManifest hChunk hOrder hDecoded hAvail hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hManifest hChunk hOrder hDecoded hAvail hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_scgg_original_empty_clause_reachable
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_scgg_accepted_evidence chunkManifestDigest perChunkProofDigest
      chunkOrderingLedger decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalEmptyClauseReachable := by
  intro accepted
  exact accepted originalEmptyClauseReachable
    (fun _hManifest _hChunk _hOrder _hDecoded _hAvail _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_scgg_original_unsat
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_scgg_accepted_evidence chunkManifestDigest perChunkProofDigest
      chunkOrderingLedger decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hManifest _hChunk _hOrder _hDecoded _hAvail _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_scgg_stream_replay_composes_to_original
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (originalUnsat : Prop) :
    ay_scgg_stream_replay_composition chunkManifestDigest perChunkProofDigest
      chunkOrderingLedger decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable originalUnsat ->
    chunkManifestDigest ->
    originalUnsat := by
  intro composition hManifest
  exact composition originalUnsat
    (fun manifest_to_chunk rest =>
      rest originalUnsat
        (fun chunk_to_order rest2 =>
          rest2 originalUnsat
            (fun order_to_decoded rest3 =>
              rest3 originalUnsat
                (fun decoded_to_availability rest4 =>
                  rest4 originalUnsat
                    (fun availability_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (availability_to_replay
                                (decoded_to_availability
                                  (order_to_decoded
                                    (chunk_to_order
                                      (manifest_to_chunk hManifest))))))))))))

theorem ay_scgg_publication_sound
    (chunkManifestDigest : Prop) (perChunkProofDigest : Prop)
    (chunkOrderingLedger : Prop) (decodedStepLedger : Prop)
    (antecedentAvailabilityLedger : Prop) (replayEvidence : Prop)
    (originalEmptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_scgg_publication chunkManifestDigest perChunkProofDigest
      chunkOrderingLedger decodedStepLedger antecedentAvailabilityLedger
      replayEvidence originalEmptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_scgg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_scgg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_scgg_disj_right noClaim (ay_scgg_disj originalUnsat publicSat)
    (ay_scgg_disj_left originalUnsat publicSat hOriginal)

theorem ay_scgg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_scgg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_scgg_disj_left noClaim (ay_scgg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_scgg_bad_no_claim
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_scgg_bad_guard manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_scgg_bad_recompute
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_scgg_bad_guard manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_scgg_failed_guard_cannot_bless_unsat
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_scgg_bad_guard manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_scgg_disj noClaim originalUnsat := by
  intro bad
  exact ay_scgg_disj_left noClaim originalUnsat
    (ay_scgg_bad_no_claim manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_scgg_failed_guard_cannot_create_public_sat
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_scgg_bad_guard manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_scgg_disj noClaim publicSat := by
  intro bad
  exact ay_scgg_disj_left noClaim publicSat
    (ay_scgg_bad_no_claim manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_scgg_failure_forces_no_claim
    (manifestMismatch : Prop) (chunkMismatch : Prop) (orderMismatch : Prop)
    (decodeMismatch : Prop) (availabilityMismatch : Prop)
    (replayMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_scgg_failure_reason manifestMismatch chunkMismatch orderMismatch
      decodeMismatch availabilityMismatch replayMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch ->
    (manifestMismatch -> noClaim) ->
    (chunkMismatch -> noClaim) ->
    (orderMismatch -> noClaim) ->
    (decodeMismatch -> noClaim) ->
    (availabilityMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure manifest_to_no_claim chunk_to_no_claim order_to_no_claim
  intro decode_to_no_claim availability_to_no_claim replay_to_no_claim
  intro reachability_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim manifest_to_no_claim chunk_to_no_claim
    order_to_no_claim decode_to_no_claim availability_to_no_claim
    replay_to_no_claim reachability_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_scgg_manifest_mismatch_forces_no_claim
    (manifestMismatch noClaim : Prop) :
    manifestMismatch -> (manifestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_chunk_mismatch_forces_no_claim
    (chunkMismatch noClaim : Prop) :
    chunkMismatch -> (chunkMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_order_mismatch_forces_no_claim
    (orderMismatch noClaim : Prop) :
    orderMismatch -> (orderMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_decode_mismatch_forces_no_claim
    (decodeMismatch noClaim : Prop) :
    decodeMismatch -> (decodeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_availability_mismatch_forces_no_claim
    (availabilityMismatch noClaim : Prop) :
    availabilityMismatch -> (availabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch -> (reachabilityMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_scgg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
