-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof parser-tokenization guard soundness for ay sequential-main SAT-COMP
-- UNSAT proof publication. Propositions stand for raw proof digests, tokenizer
-- manifests, parsed token ledgers, parsed proof ledgers, antecedent
-- availability, proof replay, empty-clause reachability witnesses, checker
-- transcripts, benchmark fingerprints, build/archive evidence, fallback
-- no-claim paths, audit transcripts, and fail-closed recompute diagnostics.

def ay_ptkg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ptkg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ptkg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ptkg_accepted_evidence
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (rawProofDigest ->
      tokenizerManifest ->
      parsedTokenLedger ->
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

def ay_ptkg_parse_replay_composition
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :=
  ay_ptkg_conj
    (ay_ptkg_map rawProofDigest tokenizerManifest)
    (ay_ptkg_conj
      (ay_ptkg_map tokenizerManifest parsedTokenLedger)
      (ay_ptkg_conj
        (ay_ptkg_map parsedTokenLedger parsedProofLedger)
        (ay_ptkg_conj
          (ay_ptkg_map parsedProofLedger antecedentAvailabilityWitness)
          (ay_ptkg_conj
            (ay_ptkg_map antecedentAvailabilityWitness proofReplay)
            (ay_ptkg_conj
              (ay_ptkg_map proofReplay emptyClauseReachabilityWitness)
              (ay_ptkg_map emptyClauseReachabilityWitness originalUnsat)))))))

def ay_ptkg_publication
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_ptkg_conj
    (ay_ptkg_accepted_evidence rawProofDigest tokenizerManifest
      parsedTokenLedger parsedProofLedger antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat)
    originalUnsat

def ay_ptkg_failure_reason
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (rawMismatch -> result) ->
    (tokenMismatch -> result) ->
    (parseMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ptkg_bad_guard
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ptkg_conj
    (ay_ptkg_conj noClaim recompute)
    (ay_ptkg_failure_reason rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch)

def ay_ptkg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ptkg_disj noClaim (ay_ptkg_disj originalUnsat publicSat)

theorem ay_ptkg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ptkg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ptkg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ptkg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ptkg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ptkg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ptkg_build_accepted_evidence
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    rawProofDigest ->
    tokenizerManifest ->
    parsedTokenLedger ->
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
    ay_ptkg_accepted_evidence rawProofDigest tokenizerManifest
      parsedTokenLedger parsedProofLedger antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat := by
  intro hRaw hTokenizer hTokens hParsed hAntecedent hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hRaw hTokenizer hTokens hParsed hAntecedent hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_ptkg_empty_clause_reachable
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_ptkg_accepted_evidence rawProofDigest tokenizerManifest
      parsedTokenLedger parsedProofLedger antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hRaw _hTokenizer _hTokens _hParsed _hAntecedent _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_ptkg_original_unsat
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_ptkg_accepted_evidence rawProofDigest tokenizerManifest
      parsedTokenLedger parsedProofLedger antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hRaw _hTokenizer _hTokens _hParsed _hAntecedent _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_ptkg_parse_replay_composes_to_original
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :
    ay_ptkg_parse_replay_composition rawProofDigest tokenizerManifest
      parsedTokenLedger parsedProofLedger antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness originalUnsat ->
    rawProofDigest ->
    originalUnsat := by
  intro composition hRaw
  exact composition originalUnsat
    (fun raw_to_tokenizer rest =>
      rest originalUnsat
        (fun tokenizer_to_tokens rest2 =>
          rest2 originalUnsat
            (fun tokens_to_parsed rest3 =>
              rest3 originalUnsat
                (fun parsed_to_antecedent rest4 =>
                  rest4 originalUnsat
                    (fun antecedent_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (antecedent_to_replay
                                (parsed_to_antecedent
                                  (tokens_to_parsed
                                    (tokenizer_to_tokens
                                      (raw_to_tokenizer hRaw))))))))))))

theorem ay_ptkg_publication_sound
    (rawProofDigest : Prop) (tokenizerManifest : Prop)
    (parsedTokenLedger : Prop) (parsedProofLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_ptkg_publication rawProofDigest tokenizerManifest parsedTokenLedger
      parsedProofLedger antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ptkg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ptkg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_ptkg_disj_right noClaim (ay_ptkg_disj originalUnsat publicSat)
    (ay_ptkg_disj_left originalUnsat publicSat hOriginal)

theorem ay_ptkg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ptkg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ptkg_disj_left noClaim (ay_ptkg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_ptkg_bad_no_claim
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ptkg_bad_guard rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ptkg_bad_recompute
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ptkg_bad_guard rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ptkg_failed_guard_cannot_bless_unsat
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_ptkg_bad_guard rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_ptkg_disj noClaim originalUnsat := by
  intro bad
  exact ay_ptkg_disj_left noClaim originalUnsat
    (ay_ptkg_bad_no_claim rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_ptkg_failed_guard_cannot_create_public_sat
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_ptkg_bad_guard rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_ptkg_disj noClaim publicSat := by
  intro bad
  exact ay_ptkg_disj_left noClaim publicSat
    (ay_ptkg_bad_no_claim rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_ptkg_failure_forces_no_claim
    (rawMismatch : Prop) (tokenMismatch : Prop) (parseMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ptkg_failure_reason rawMismatch tokenMismatch parseMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch ->
    (rawMismatch -> noClaim) ->
    (tokenMismatch -> noClaim) ->
    (parseMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure raw_to_no_claim token_to_no_claim parse_to_no_claim
  intro antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim raw_to_no_claim token_to_no_claim parse_to_no_claim
    antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_ptkg_raw_mismatch_forces_no_claim
    (rawMismatch noClaim : Prop) :
    rawMismatch -> (rawMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_token_mismatch_forces_no_claim
    (tokenMismatch noClaim : Prop) :
    tokenMismatch -> (tokenMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_parse_mismatch_forces_no_claim
    (parseMismatch noClaim : Prop) :
    parseMismatch -> (parseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ptkg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
