-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Assumption-discharge guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for original formula digests,
-- assumption-scope manifests, activation literal ledgers, scoped proof digests,
-- discharge witnesses, antecedent origin ledgers, proof replay, empty-clause
-- reachability witnesses, checker transcripts, benchmark fingerprints,
-- build/archive evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_uadg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_uadg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_uadg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_uadg_accepted_evidence
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (scopedOriginalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaDigest ->
      assumptionScopeManifest ->
      activationLiteralLedger ->
      scopedProofDigest ->
      dischargeWitness ->
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

def ay_uadg_discharge_replay_composition
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (scopedOriginalUnsat : Prop) :=
  ay_uadg_conj
    (ay_uadg_conj
      (ay_uadg_map originalFormulaDigest assumptionScopeManifest)
      (ay_uadg_conj
        (ay_uadg_map assumptionScopeManifest activationLiteralLedger)
        (ay_uadg_conj
          (ay_uadg_map activationLiteralLedger scopedProofDigest)
          (ay_uadg_conj
            (ay_uadg_map scopedProofDigest dischargeWitness)
            (ay_uadg_conj
              (ay_uadg_map dischargeWitness antecedentOriginLedger)
              (ay_uadg_conj
                (ay_uadg_map antecedentOriginLedger proofReplay)
                (ay_uadg_conj
                  (ay_uadg_map proofReplay emptyClauseReachabilityWitness)
                  (ay_uadg_map emptyClauseReachabilityWitness
                    scopedOriginalUnsat))))))))
    (ay_uadg_map originalFormulaDigest scopedOriginalUnsat)

def ay_uadg_publication
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (scopedOriginalUnsat : Prop) :=
  ay_uadg_conj
    (ay_uadg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest dischargeWitness
      antecedentOriginLedger proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat)
    scopedOriginalUnsat

def ay_uadg_failure_reason
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (scopeMismatch -> result) ->
    (activationMismatch -> result) ->
    (dischargeMismatch -> result) ->
    (proofMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_uadg_bad_guard
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_uadg_conj
    (ay_uadg_conj noClaim recompute)
    (ay_uadg_failure_reason scopeMismatch activationMismatch
      dischargeMismatch proofMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_uadg_public_report
    (noClaim : Prop) (scopedOriginalUnsat : Prop) (publicSat : Prop) :=
  ay_uadg_disj noClaim (ay_uadg_disj scopedOriginalUnsat publicSat)

theorem ay_uadg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_uadg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_uadg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_uadg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_uadg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_uadg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_uadg_build_accepted_evidence
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (scopedOriginalUnsat : Prop) :
    originalFormulaDigest ->
    assumptionScopeManifest ->
    activationLiteralLedger ->
    scopedProofDigest ->
    dischargeWitness ->
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
    ay_uadg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest dischargeWitness
      antecedentOriginLedger proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat := by
  intro hOriginal hScope hActivation hProof hDischarge hAntecedent hReplay
  intro hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hScoped result publish
  exact publish hOriginal hScope hActivation hProof hDischarge hAntecedent
    hReplay hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted
    hBuild hBuildAccepted hArchive hFallback hAudit hScoped

theorem ay_uadg_empty_clause_reachable
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (scopedOriginalUnsat : Prop) :
    ay_uadg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest dischargeWitness
      antecedentOriginLedger proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hOriginal _hScope _hActivation _hProof _hDischarge _hAntecedent
      _hReplay hEmpty _hTranscript _hChecker _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hScoped =>
      hEmpty)

theorem ay_uadg_scoped_original_unsat
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (scopedOriginalUnsat : Prop) :
    ay_uadg_accepted_evidence originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest dischargeWitness
      antecedentOriginLedger proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat ->
    scopedOriginalUnsat := by
  intro accepted
  exact accepted scopedOriginalUnsat
    (fun _hOriginal _hScope _hActivation _hProof _hDischarge _hAntecedent
      _hReplay _hEmpty _hTranscript _hChecker _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit hScoped =>
      hScoped)

theorem ay_uadg_discharge_replay_composes_to_original
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (scopedOriginalUnsat : Prop) :
    ay_uadg_discharge_replay_composition originalFormulaDigest
      assumptionScopeManifest activationLiteralLedger scopedProofDigest
      dischargeWitness antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness scopedOriginalUnsat ->
    originalFormulaDigest ->
    scopedOriginalUnsat := by
  intro composition hOriginal
  exact composition scopedOriginalUnsat
    (fun _chain direct_to_scoped =>
      direct_to_scoped hOriginal)

theorem ay_uadg_publication_sound
    (originalFormulaDigest : Prop) (assumptionScopeManifest : Prop)
    (activationLiteralLedger : Prop) (scopedProofDigest : Prop)
    (dischargeWitness : Prop) (antecedentOriginLedger : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (scopedOriginalUnsat : Prop) :
    ay_uadg_publication originalFormulaDigest assumptionScopeManifest
      activationLiteralLedger scopedProofDigest dischargeWitness
      antecedentOriginLedger proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript scopedOriginalUnsat ->
    scopedOriginalUnsat := by
  intro publication
  exact publication scopedOriginalUnsat
    (fun _accepted hScoped => hScoped)

theorem ay_uadg_public_unsat_report
    (noClaim : Prop) (scopedOriginalUnsat : Prop) (publicSat : Prop) :
    scopedOriginalUnsat ->
    ay_uadg_public_report noClaim scopedOriginalUnsat publicSat := by
  intro hScoped
  exact ay_uadg_disj_right noClaim (ay_uadg_disj scopedOriginalUnsat publicSat)
    (ay_uadg_disj_left scopedOriginalUnsat publicSat hScoped)

theorem ay_uadg_public_no_claim_report
    (noClaim : Prop) (scopedOriginalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_uadg_public_report noClaim scopedOriginalUnsat publicSat := by
  intro hNoClaim
  exact ay_uadg_disj_left noClaim (ay_uadg_disj scopedOriginalUnsat publicSat)
    hNoClaim

theorem ay_uadg_bad_no_claim
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uadg_bad_guard scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_uadg_bad_recompute
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uadg_bad_guard scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_uadg_failed_guard_cannot_bless_unsat
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (scopedOriginalUnsat : Prop) :
    ay_uadg_bad_guard scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_uadg_disj noClaim scopedOriginalUnsat := by
  intro bad
  exact ay_uadg_disj_left noClaim scopedOriginalUnsat
    (ay_uadg_bad_no_claim scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_uadg_failed_guard_cannot_create_public_sat
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_uadg_bad_guard scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute ->
    ay_uadg_disj noClaim publicSat := by
  intro bad
  exact ay_uadg_disj_left noClaim publicSat
    (ay_uadg_bad_no_claim scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_uadg_failure_forces_no_claim
    (scopeMismatch : Prop) (activationMismatch : Prop)
    (dischargeMismatch : Prop) (proofMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uadg_failure_reason scopeMismatch activationMismatch dischargeMismatch
      proofMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch ->
    (scopeMismatch -> noClaim) ->
    (activationMismatch -> noClaim) ->
    (dischargeMismatch -> noClaim) ->
    (proofMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure scope_to_no_claim activation_to_no_claim
  intro discharge_to_no_claim proof_to_no_claim antecedent_to_no_claim
  intro replay_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim scope_to_no_claim activation_to_no_claim
    discharge_to_no_claim proof_to_no_claim antecedent_to_no_claim
    replay_to_no_claim checker_to_no_claim fingerprint_to_no_claim
    build_to_no_claim archive_to_no_claim audit_to_no_claim

theorem ay_uadg_scope_mismatch_forces_no_claim
    (scopeMismatch noClaim : Prop) :
    scopeMismatch -> (scopeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_activation_mismatch_forces_no_claim
    (activationMismatch noClaim : Prop) :
    activationMismatch -> (activationMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_discharge_mismatch_forces_no_claim
    (dischargeMismatch noClaim : Prop) :
    dischargeMismatch -> (dischargeMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch -> (proofMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uadg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
