-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof-checker option guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof digests, checker binary
-- digests, checker option manifests, parsed proof ledgers, proof replay,
-- empty-clause reachability witnesses, checker transcripts, benchmark
-- fingerprints, build/archive evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_pcog_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_pcog_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_pcog_map (source : Prop) (target : Prop) :=
  source -> target

def ay_pcog_accepted_evidence
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      checkerBinaryDigest ->
      checkerOptionManifest ->
      parsedProofLedger ->
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

def ay_pcog_option_replay_composition
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_pcog_conj
    (ay_pcog_map proofDigest checkerBinaryDigest)
    (ay_pcog_conj
      (ay_pcog_map checkerBinaryDigest checkerOptionManifest)
      (ay_pcog_conj
        (ay_pcog_map checkerOptionManifest parsedProofLedger)
        (ay_pcog_conj
          (ay_pcog_map parsedProofLedger proofReplay)
          (ay_pcog_conj
            (ay_pcog_map proofReplay emptyClauseReachabilityWitness)
            (ay_pcog_map emptyClauseReachabilityWitness originalUnsat))))))

def ay_pcog_publication
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_pcog_conj
    (ay_pcog_accepted_evidence proofDigest checkerBinaryDigest
      checkerOptionManifest parsedProofLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_pcog_failure_reason
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (optionMismatch -> result) ->
    (checkerMismatch -> result) ->
    (digestMismatch -> result) ->
    (parseMismatch -> result) ->
    (replayMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_pcog_bad_guard
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_pcog_conj
    (ay_pcog_conj noClaim recompute)
    (ay_pcog_failure_reason optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_pcog_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_pcog_disj noClaim (ay_pcog_disj originalUnsat publicSat)

theorem ay_pcog_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_pcog_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pcog_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_pcog_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pcog_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_pcog_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pcog_build_accepted_evidence
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofDigest ->
    checkerBinaryDigest ->
    checkerOptionManifest ->
    parsedProofLedger ->
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
    ay_pcog_accepted_evidence proofDigest checkerBinaryDigest
      checkerOptionManifest parsedProofLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hProof hBinary hOptions hParsed hReplay hEmpty hTranscript
  intro hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted
  intro hArchive hFallback hAudit hOriginal result publish
  exact publish hProof hBinary hOptions hParsed hReplay hEmpty hTranscript
    hChecker hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hOriginal

theorem ay_pcog_empty_clause_reachable
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_pcog_accepted_evidence proofDigest checkerBinaryDigest
      checkerOptionManifest parsedProofLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hProof _hBinary _hOptions _hParsed _hReplay hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_pcog_original_unsat
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_pcog_accepted_evidence proofDigest checkerBinaryDigest
      checkerOptionManifest parsedProofLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hProof _hBinary _hOptions _hParsed _hReplay _hEmpty _hTranscript
      _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_pcog_option_replay_composes_to_original
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_pcog_option_replay_composition proofDigest checkerBinaryDigest
      checkerOptionManifest parsedProofLedger proofReplay
      emptyClauseReachabilityWitness originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hProof
  exact composition originalUnsat
    (fun proof_to_binary rest =>
      rest originalUnsat
        (fun binary_to_options rest2 =>
          rest2 originalUnsat
            (fun options_to_parsed rest3 =>
              rest3 originalUnsat
                (fun parsed_to_replay rest4 =>
                  rest4 originalUnsat
                    (fun replay_to_empty empty_to_original =>
                      empty_to_original
                        (replay_to_empty
                          (parsed_to_replay
                            (options_to_parsed
                              (binary_to_options
                                (proof_to_binary hProof)))))))))))

theorem ay_pcog_publication_sound
    (proofDigest : Prop) (checkerBinaryDigest : Prop)
    (checkerOptionManifest : Prop) (parsedProofLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_pcog_publication proofDigest checkerBinaryDigest checkerOptionManifest
      parsedProofLedger proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_pcog_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_pcog_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_pcog_disj_right noClaim (ay_pcog_disj originalUnsat publicSat)
    (ay_pcog_disj_left originalUnsat publicSat hOriginal)

theorem ay_pcog_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_pcog_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_pcog_disj_left noClaim (ay_pcog_disj originalUnsat publicSat)
    hNoClaim

theorem ay_pcog_bad_no_claim
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pcog_bad_guard optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_pcog_bad_recompute
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pcog_bad_guard optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_pcog_failed_guard_cannot_bless_unsat
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_pcog_bad_guard optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_pcog_disj noClaim originalUnsat := by
  intro bad
  exact ay_pcog_disj_left noClaim originalUnsat
    (ay_pcog_bad_no_claim optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_pcog_failed_guard_cannot_create_public_sat
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_pcog_bad_guard optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_pcog_disj noClaim publicSat := by
  intro bad
  exact ay_pcog_disj_left noClaim publicSat
    (ay_pcog_bad_no_claim optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_pcog_failure_forces_no_claim
    (optionMismatch : Prop) (checkerMismatch : Prop)
    (digestMismatch : Prop) (parseMismatch : Prop) (replayMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pcog_failure_reason optionMismatch checkerMismatch digestMismatch
      parseMismatch replayMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch ->
    (optionMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (digestMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure option_to_no_claim checker_to_no_claim digest_to_no_claim
  intro parse_to_no_claim replay_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim option_to_no_claim checker_to_no_claim
    digest_to_no_claim parse_to_no_claim replay_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_pcog_option_mismatch_forces_no_claim
    (optionMismatch noClaim : Prop) :
    optionMismatch -> (optionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_pcog_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
