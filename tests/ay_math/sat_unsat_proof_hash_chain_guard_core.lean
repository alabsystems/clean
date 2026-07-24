-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof hash-chain integrity guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for proof digests, per-line
-- hash-chain manifests, parsed proof ledgers, antecedent availability,
-- proof replay, empty-clause reachability witnesses, checker transcripts,
-- benchmark fingerprints, build/archive evidence, fallback no-claim paths,
-- audit transcripts, and fail-closed recompute diagnostics.

def ay_phcg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_phcg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_phcg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_phcg_accepted_evidence
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      hashChainManifest ->
      parsedProofLedger ->
      antecedentAvailabilityWitness ->
      proofReplay ->
      emptyClauseReachabilityWitness ->
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

def ay_phcg_hash_chain_composition
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_phcg_conj
    (ay_phcg_map proofDigest hashChainManifest)
    (ay_phcg_conj
      (ay_phcg_map hashChainManifest parsedProofLedger)
      (ay_phcg_conj
        (ay_phcg_map parsedProofLedger antecedentAvailabilityWitness)
        (ay_phcg_conj
          (ay_phcg_map antecedentAvailabilityWitness proofReplay)
          (ay_phcg_conj
            (ay_phcg_map proofReplay emptyClauseReachabilityWitness)
            (ay_phcg_map emptyClauseReachabilityWitness originalUnsat))))))

def ay_phcg_publication
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_phcg_conj
    (ay_phcg_accepted_evidence proofDigest hashChainManifest
      parsedProofLedger antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_phcg_failure_reason
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (hashMismatch -> result) ->
    (parseMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_phcg_bad_guard
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_phcg_conj
    (ay_phcg_conj noClaim recompute)
    (ay_phcg_failure_reason digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch)

def ay_phcg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_phcg_disj noClaim (ay_phcg_disj originalUnsat publicSat)

theorem ay_phcg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_phcg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_phcg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_phcg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_phcg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_phcg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_phcg_build_accepted_evidence
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofDigest ->
    hashChainManifest ->
    parsedProofLedger ->
    antecedentAvailabilityWitness ->
    proofReplay ->
    emptyClauseReachabilityWitness ->
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
    ay_phcg_accepted_evidence proofDigest hashChainManifest
      parsedProofLedger antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hDigest hHash hParsed hAntecedent hReplay hEmpty hTranscript
  intro hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted
  intro hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hHash hParsed hAntecedent hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_phcg_empty_clause_reachable
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_phcg_accepted_evidence proofDigest hashChainManifest
      parsedProofLedger antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hDigest _hHash _hParsed _hAntecedent _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_phcg_original_unsat
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_phcg_accepted_evidence proofDigest hashChainManifest
      parsedProofLedger antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hHash _hParsed _hAntecedent _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_phcg_hash_chain_composes_to_original
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_phcg_hash_chain_composition proofDigest hashChainManifest
      parsedProofLedger antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_hash rest =>
      rest originalUnsat
        (fun hash_to_parsed rest2 =>
          rest2 originalUnsat
            (fun parsed_to_antecedent rest3 =>
              rest3 originalUnsat
                (fun antecedent_to_replay rest4 =>
                  rest4 originalUnsat
                    (fun replay_to_empty empty_to_original =>
                      empty_to_original
                        (replay_to_empty
                          (antecedent_to_replay
                            (parsed_to_antecedent
                              (hash_to_parsed
                                (digest_to_hash hDigest)))))))))))

theorem ay_phcg_publication_sound
    (proofDigest : Prop) (hashChainManifest : Prop)
    (parsedProofLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_phcg_publication proofDigest hashChainManifest parsedProofLedger
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_phcg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_phcg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_phcg_disj_right noClaim (ay_phcg_disj originalUnsat publicSat)
    (ay_phcg_disj_left originalUnsat publicSat hOriginal)

theorem ay_phcg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_phcg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_phcg_disj_left noClaim (ay_phcg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_phcg_bad_no_claim
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_phcg_bad_guard digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_phcg_bad_recompute
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_phcg_bad_guard digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_phcg_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_phcg_bad_guard digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_phcg_disj noClaim originalUnsat := by
  intro bad
  exact ay_phcg_disj_left noClaim originalUnsat
    (ay_phcg_bad_no_claim digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_phcg_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_phcg_bad_guard digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_phcg_disj noClaim publicSat := by
  intro bad
  exact ay_phcg_disj_left noClaim publicSat
    (ay_phcg_bad_no_claim digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_phcg_failure_forces_no_claim
    (digestMismatch : Prop) (hashMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_phcg_failure_reason digestMismatch hashMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch ->
    (digestMismatch -> noClaim) ->
    (hashMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim hash_to_no_claim parse_to_no_claim
  intro antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim digest_to_no_claim hash_to_no_claim parse_to_no_claim
    antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_phcg_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_hash_mismatch_forces_no_claim
    (hashMismatch noClaim : Prop) :
    hashMismatch -> (hashMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_phcg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
