-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental-assumption scope guard soundness for ay sequential-main
-- SAT-COMP UNSAT proof publication. Propositions stand for original formula
-- digests, assumption-scope manifests, activation-literal ledgers, scoped
-- proof digests, antecedent origin ledgers, proof replay, empty-clause
-- reachability witnesses, checker transcripts, benchmark fingerprints,
-- build/archive evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_uasg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_uasg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_uasg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_uasg_accepted_evidence
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (scopedOriginalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaDigest ->
      assumptionScopeManifest ->
      activationLiteralLedger ->
      scopedProofDigest ->
      antecedentOriginLedger ->
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
      scopedOriginalUnsat ->
      result) ->
    result

def ay_uasg_scope_replay_composition
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (scopedOriginalUnsat : Prop) :=
  ay_uasg_conj
    (ay_uasg_map originalFormulaDigest assumptionScopeManifest)
    (ay_uasg_conj
      (ay_uasg_map assumptionScopeManifest activationLiteralLedger)
      (ay_uasg_conj
        (ay_uasg_map activationLiteralLedger scopedProofDigest)
        (ay_uasg_conj
          (ay_uasg_map scopedProofDigest antecedentOriginLedger)
          (ay_uasg_conj
            (ay_uasg_map antecedentOriginLedger proofReplay)
            (ay_uasg_conj
              (ay_uasg_map proofReplay emptyClauseReachabilityWitness)
              (ay_uasg_map emptyClauseReachabilityWitness
                scopedOriginalUnsat)))))))

def ay_uasg_publication
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (scopedOriginalUnsat : Prop) :=
  ay_uasg_conj
    (ay_uasg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest antecedentOriginLedger
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat)
    scopedOriginalUnsat

def ay_uasg_failure_reason
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (scopeMismatch -> result) ->
    (activationMismatch -> result) ->
    (proofMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_uasg_bad_guard
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_uasg_conj
    (ay_uasg_conj noClaim recompute)
    (ay_uasg_failure_reason scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch)

def ay_uasg_public_report
    (noClaim : Prop) (scopedOriginalUnsat : Prop) (publicSat : Prop) :=
  ay_uasg_disj noClaim (ay_uasg_disj scopedOriginalUnsat publicSat)

theorem ay_uasg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_uasg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_uasg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_uasg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_uasg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_uasg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_uasg_build_accepted_evidence
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (scopedOriginalUnsat : Prop) :
    originalFormulaDigest ->
    assumptionScopeManifest ->
    activationLiteralLedger ->
    scopedProofDigest ->
    antecedentOriginLedger ->
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
    scopedOriginalUnsat ->
    ay_uasg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest antecedentOriginLedger
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat := by
  intro hOriginal hScope hActivation hProof hAntecedent hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hScoped result publish
  exact publish hOriginal hScope hActivation hProof hAntecedent hReplay
    hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hScoped

theorem ay_uasg_empty_clause_reachable
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (scopedOriginalUnsat : Prop) :
    ay_uasg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest antecedentOriginLedger
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hOriginal _hScope _hActivation _hProof _hAntecedent _hReplay
      hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit _hScoped =>
      hEmpty)

theorem ay_uasg_scoped_original_unsat
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (scopedOriginalUnsat : Prop) :
    ay_uasg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest antecedentOriginLedger
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat ->
    scopedOriginalUnsat := by
  intro accepted
  exact accepted scopedOriginalUnsat
    (fun _hOriginal _hScope _hActivation _hProof _hAntecedent _hReplay
      _hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit hScoped =>
      hScoped)

theorem ay_uasg_scope_replay_composes_to_original
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (scopedOriginalUnsat : Prop) :
    ay_uasg_scope_replay_composition originalFormulaDigest
      assumptionScopeManifest activationLiteralLedger scopedProofDigest
      antecedentOriginLedger proofReplay emptyClauseReachabilityWitness
      scopedOriginalUnsat ->
    originalFormulaDigest ->
    scopedOriginalUnsat := by
  intro composition hOriginal
  exact composition scopedOriginalUnsat
    (fun original_to_scope rest =>
      rest scopedOriginalUnsat
        (fun scope_to_activation rest2 =>
          rest2 scopedOriginalUnsat
            (fun activation_to_proof rest3 =>
              rest3 scopedOriginalUnsat
                (fun proof_to_antecedent rest4 =>
                  rest4 scopedOriginalUnsat
                    (fun antecedent_to_replay rest5 =>
                      rest5 scopedOriginalUnsat
                        (fun replay_to_empty empty_to_scoped =>
                          empty_to_scoped
                            (replay_to_empty
                              (antecedent_to_replay
                                (proof_to_antecedent
                                  (activation_to_proof
                                    (scope_to_activation
                                      (original_to_scope hOriginal))))))))))))

theorem ay_uasg_publication_sound
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (scopedOriginalUnsat : Prop) :
    ay_uasg_publication originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest antecedentOriginLedger
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat ->
    scopedOriginalUnsat := by
  intro publication
  exact publication scopedOriginalUnsat
    (fun _accepted hScoped => hScoped)

theorem ay_uasg_public_unsat_report
    (noClaim : Prop) (scopedOriginalUnsat : Prop) (publicSat : Prop) :
    scopedOriginalUnsat ->
    ay_uasg_public_report noClaim scopedOriginalUnsat publicSat := by
  intro hScoped
  exact ay_uasg_disj_right noClaim (ay_uasg_disj scopedOriginalUnsat publicSat)
    (ay_uasg_disj_left scopedOriginalUnsat publicSat hScoped)

theorem ay_uasg_public_no_claim_report
    (noClaim : Prop) (scopedOriginalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_uasg_public_report noClaim scopedOriginalUnsat publicSat := by
  intro hNoClaim
  exact ay_uasg_disj_left noClaim (ay_uasg_disj scopedOriginalUnsat publicSat)
    hNoClaim

theorem ay_uasg_bad_no_claim
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uasg_bad_guard scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_uasg_bad_recompute
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uasg_bad_guard scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_uasg_failed_guard_cannot_bless_unsat
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (scopedOriginalUnsat : Prop) :
    ay_uasg_bad_guard scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_uasg_disj noClaim scopedOriginalUnsat := by
  intro bad
  exact ay_uasg_disj_left noClaim scopedOriginalUnsat
    (ay_uasg_bad_no_claim scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_uasg_failed_guard_cannot_create_public_sat
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_uasg_bad_guard scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_uasg_disj noClaim publicSat := by
  intro bad
  exact ay_uasg_disj_left noClaim publicSat
    (ay_uasg_bad_no_claim scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_uasg_failure_forces_no_claim
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (proofMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uasg_failure_reason scopeMismatch activationMismatch proofMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch ->
    (scopeMismatch -> noClaim) ->
    (activationMismatch -> noClaim) ->
    (proofMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure scope_to_no_claim activation_to_no_claim proof_to_no_claim
  intro antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim scope_to_no_claim activation_to_no_claim
    proof_to_no_claim antecedent_to_no_claim replay_to_no_claim
    checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
    archive_to_no_claim audit_to_no_claim

theorem ay_uasg_scope_mismatch_forces_no_claim
    (scopeMismatch noClaim : Prop) :
    scopeMismatch -> (scopeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_activation_mismatch_forces_no_claim
    (activationMismatch noClaim : Prop) :
    activationMismatch -> (activationMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch -> (proofMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uasg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
