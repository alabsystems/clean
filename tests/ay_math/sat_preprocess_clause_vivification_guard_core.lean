-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-vivification guard soundness.
-- The propositions stand for source-clause manifests, failed-literal/unit-propagation replay witnesses, strengthened-clause
-- ledgers, removed-literal coverage digests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_cvig_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cvig_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cvig_Equisat (before : Prop) (after : Prop) :=
  ay_cvig_Conj (before -> after) (after -> before)

def ay_cvig_Sat (cnf : Prop) (model : Prop) :=
  ay_cvig_Conj cnf model

def ay_cvig_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cvig_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_cvig_Conj (leftId -> rightId) (rightId -> leftId)

def ay_cvig_SourceClauseManifest
    (sourceClause : Prop) (sourceManifestAccepted : Prop)
    (sourceClauseManifest : Prop) :=
  ay_cvig_Conj sourceClauseManifest (sourceClause -> sourceManifestAccepted)

def ay_cvig_FailedLiteralUnitPropagationReplayWitness
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop)
    (unitPropagationReplayWitness : Prop) :=
  ay_cvig_Conj unitPropagationReplayWitness (failedLiteralReplay -> unitPropagationAccepted)

def ay_cvig_RemovedLiteralCoverageDigest
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop)
    (removedLiteralCoverageWitness : Prop) :=
  ay_cvig_Conj removedLiteralCoverageWitness (removedLiteralSet -> removedLiteralCoverageAccepted)

def ay_cvig_StrengthenedClauseLedger
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop) :=
  ay_cvig_Conj strengthenedClauseLedger (strengthenedClause -> strengtheningRecorded)

def ay_cvig_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_cvig_Sat replayedCnf replayedModel ->
    ay_cvig_Sat originalCnf originalModel

def ay_cvig_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cvig_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cvig_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cvig_Conj
    (ay_cvig_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cvig_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_cvig_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_cvig_Conj fingerprintWitness
    (ay_cvig_IdMatch originalFingerprint replayedFingerprint)

def ay_cvig_CheckerReplay
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_cvig_Conj vivificationReplayCertificate checkerAccepted

def ay_cvig_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cvig_Conj baselineSolver baselineAvailable

def ay_cvig_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cvig_Conj binaryFingerprint buildReproducible

def ay_cvig_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cvig_Conj validatorAccepted validatorVersion

def ay_cvig_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cvig_Conj auditAppended auditAppendOnly

def ay_cvig_AcceptedClauseVivificationGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (sourceClause : Prop) (sourceManifestAccepted : Prop) (sourceClauseManifest : Prop)
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop) (unitPropagationReplayWitness : Prop)
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop) (removedLiteralCoverageWitness : Prop)
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cvig_SourceClauseManifest
       sourceClause sourceManifestAccepted sourceClauseManifest ->
     ay_cvig_FailedLiteralUnitPropagationReplayWitness
       failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness ->
     ay_cvig_RemovedLiteralCoverageDigest
       removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness ->
     ay_cvig_StrengthenedClauseLedger
       strengthenedClause strengtheningRecorded strengthenedClauseLedger ->
     ay_cvig_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_cvig_Equisat originalCnf replayedCnf ->
     ay_cvig_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_cvig_CheckerReplay vivificationReplayCertificate checkerAccepted ->
     ay_cvig_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cvig_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cvig_ValidatorGate validatorAccepted validatorVersion ->
     ay_cvig_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cvig_ClauseVivificationGuardFailure
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleSourceClauseManifest -> result) ->
    (unitPropagationReplayMismatch -> result) ->
    (removedLiteralCoverageMismatch -> result) ->
    (strengthenedClauseLedgerGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_cvig_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cvig_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cvig_Conj currentCnf recompute

def ay_cvig_DiagnosticClauseVivificationGuard
    (currentCnf : Prop)
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cvig_Conj
    (ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_cvig_Conj
      (ay_cvig_RecomputeObligation currentCnf recompute)
      (ay_cvig_NoSemanticClaim diagnostic))

def ay_cvig_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cvig_Conj exitCode claim

def ay_cvig_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cvig_Disj
    (ay_cvig_ExitCodeSound exitCode (ay_cvig_Sat originalCnf model))
    (ay_cvig_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cvig_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cvig_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cvig_conj_left
    (left : Prop) (right : Prop) :
    ay_cvig_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cvig_conj_right
    (left : Prop) (right : Prop) :
    ay_cvig_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cvig_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cvig_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cvig_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cvig_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cvig_equisat_forward
    (before : Prop) (after : Prop) :
    ay_cvig_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_cvig_conj_left (before -> after) (after -> before) eqsat

theorem ay_cvig_equisat_backward
    (before : Prop) (after : Prop) :
    ay_cvig_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_cvig_conj_right (before -> after) (after -> before) eqsat

theorem ay_cvig_source_clause_manifest_applies
    (sourceClause : Prop) (sourceManifestAccepted : Prop)
    (sourceClauseManifest : Prop) :
    ay_cvig_SourceClauseManifest
      sourceClause sourceManifestAccepted sourceClauseManifest ->
    sourceClause -> sourceManifestAccepted := by
  intro digest
  exact ay_cvig_conj_right sourceClauseManifest
    (sourceClause -> sourceManifestAccepted) digest

theorem ay_cvig_failed_literal_unit_propagation_replay_witness_applies
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop)
    (unitPropagationReplayWitness : Prop) :
    ay_cvig_FailedLiteralUnitPropagationReplayWitness
      failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness ->
    failedLiteralReplay -> unitPropagationAccepted := by
  intro digest
  exact ay_cvig_conj_right unitPropagationReplayWitness
    (failedLiteralReplay -> unitPropagationAccepted) digest

theorem ay_cvig_removed_literal_coverage_digest_applies
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop)
    (removedLiteralCoverageWitness : Prop) :
    ay_cvig_RemovedLiteralCoverageDigest
      removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness ->
    removedLiteralSet -> removedLiteralCoverageAccepted := by
  intro ledger
  exact ay_cvig_conj_right removedLiteralCoverageWitness
    (removedLiteralSet -> removedLiteralCoverageAccepted) ledger

theorem ay_cvig_strengthened_clause_ledger_applies
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop) :
    ay_cvig_StrengthenedClauseLedger
      strengthenedClause strengtheningRecorded strengthenedClauseLedger ->
    strengthenedClause -> strengtheningRecorded := by
  intro coverage
  exact ay_cvig_conj_right strengthenedClauseLedger
    (strengthenedClause -> strengtheningRecorded) coverage

theorem ay_cvig_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvig_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cvig_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_cvig_conj_left
    (ay_cvig_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cvig_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cvig_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvig_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cvig_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_cvig_conj_right
    (ay_cvig_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cvig_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cvig_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (sourceClause : Prop) (sourceManifestAccepted : Prop) (sourceClauseManifest : Prop)
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop) (unitPropagationReplayWitness : Prop)
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop) (removedLiteralCoverageWitness : Prop)
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cvig_AcceptedClauseVivificationGuard
      originalCnf replayedCnf
      sourceClause sourceManifestAccepted sourceClauseManifest
      failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness
      removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness
      strengthenedClause strengtheningRecorded strengthenedClauseLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      vivificationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvig_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_cvig_Equisat originalCnf replayedCnf)
    (fun _manifest _replay _coverage _strengthened _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_cvig_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (sourceClause : Prop) (sourceManifestAccepted : Prop) (sourceClauseManifest : Prop)
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop) (unitPropagationReplayWitness : Prop)
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop) (removedLiteralCoverageWitness : Prop)
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cvig_AcceptedClauseVivificationGuard
      originalCnf replayedCnf
      sourceClause sourceManifestAccepted sourceClauseManifest
      failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness
      removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness
      strengthenedClause strengtheningRecorded strengthenedClauseLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      vivificationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvig_CheckerReplay vivificationReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_cvig_CheckerReplay vivificationReplayCertificate checkerAccepted)
    (fun _manifest _replay _coverage _strengthened _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_cvig_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (sourceClause : Prop) (sourceManifestAccepted : Prop) (sourceClauseManifest : Prop)
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop) (unitPropagationReplayWitness : Prop)
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop) (removedLiteralCoverageWitness : Prop)
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cvig_AcceptedClauseVivificationGuard
      originalCnf replayedCnf
      sourceClause sourceManifestAccepted sourceClauseManifest
      failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness
      removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness
      strengthenedClause strengtheningRecorded strengthenedClauseLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      vivificationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvig_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_cvig_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _replay _coverage _strengthened _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_cvig_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_cvig_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_cvig_Sat replayedCnf replayedModel ->
    ay_cvig_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_cvig_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cvig_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_cvig_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_cvig_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (sourceClause : Prop) (sourceManifestAccepted : Prop) (sourceClauseManifest : Prop)
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop) (unitPropagationReplayWitness : Prop)
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop) (removedLiteralCoverageWitness : Prop)
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cvig_AcceptedClauseVivificationGuard
      originalCnf replayedCnf
      sourceClause sourceManifestAccepted sourceClauseManifest
      failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness
      removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness
      strengthenedClause strengtheningRecorded strengthenedClauseLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      vivificationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvig_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_cvig_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_cvig_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _replay _coverage _strengthened reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_cvig_disj_left
        (ay_cvig_ExitCodeSound exitCode
          (ay_cvig_Sat originalCnf originalModel))
        (ay_cvig_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cvig_conj_intro exitCode
          (ay_cvig_Sat originalCnf originalModel)
          hexit
          ((ay_cvig_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_cvig_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (sourceClause : Prop) (sourceManifestAccepted : Prop) (sourceClauseManifest : Prop)
    (failedLiteralReplay : Prop) (unitPropagationAccepted : Prop) (unitPropagationReplayWitness : Prop)
    (removedLiteralSet : Prop) (removedLiteralCoverageAccepted : Prop) (removedLiteralCoverageWitness : Prop)
    (strengthenedClause : Prop) (strengtheningRecorded : Prop)
    (strengthenedClauseLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (vivificationReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cvig_AcceptedClauseVivificationGuard
      originalCnf replayedCnf
      sourceClause sourceManifestAccepted sourceClauseManifest
      failedLiteralReplay unitPropagationAccepted unitPropagationReplayWitness
      removedLiteralSet removedLiteralCoverageAccepted removedLiteralCoverageWitness
      strengthenedClause strengtheningRecorded strengthenedClauseLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      vivificationReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cvig_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_cvig_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_cvig_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _replay _coverage _strengthened reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_cvig_disj_right
        (ay_cvig_ExitCodeSound exitCode
          (ay_cvig_Sat originalCnf originalModel))
        (ay_cvig_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cvig_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_cvig_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_cvig_failure_stale_source_clause_manifest
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleSourceClauseManifest ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result source_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact source_case failure

theorem ay_cvig_failure_unit_propagation_replay
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    unitPropagationReplayMismatch ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case replay_case _coverage_case _strengthened_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact replay_case failure

theorem ay_cvig_failure_removed_literal_coverage_digest
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    removedLiteralCoverageMismatch ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_cvig_failure_strengthened_clause_ledger
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    strengthenedClauseLedgerGap ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_cvig_failure_reconstruction
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_cvig_failure_stale_fingerprint
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_cvig_failure_unchecked_replay
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_cvig_failure_missing_baseline
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_cvig_failure_build
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_cvig_failure_validator
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_cvig_failure_audit
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_cvig_ClauseVivificationGuardFailure
      staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _replay_case _coverage_case _strengthened_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_cvig_diagnostic_no_claim
    (currentCnf : Prop)
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cvig_DiagnosticClauseVivificationGuard
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cvig_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_cvig_conj_right
    (ay_cvig_RecomputeObligation currentCnf recompute)
    (ay_cvig_NoSemanticClaim diagnostic)
    (ay_cvig_conj_right
      (ay_cvig_ClauseVivificationGuardFailure
        staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cvig_Conj
        (ay_cvig_RecomputeObligation currentCnf recompute)
        (ay_cvig_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cvig_diagnostic_recompute
    (currentCnf : Prop)
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cvig_DiagnosticClauseVivificationGuard
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cvig_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_cvig_conj_left
    (ay_cvig_RecomputeObligation currentCnf recompute)
    (ay_cvig_NoSemanticClaim diagnostic)
    (ay_cvig_conj_right
      (ay_cvig_ClauseVivificationGuardFailure
        staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cvig_Conj
        (ay_cvig_RecomputeObligation currentCnf recompute)
        (ay_cvig_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cvig_unchecked_vivification_cannot_bless_public_result
    (currentCnf : Prop)
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cvig_DiagnosticClauseVivificationGuard
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cvig_Conj
      (ay_cvig_NoSemanticClaim diagnostic)
      (ay_cvig_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_cvig_conj_intro
    (ay_cvig_NoSemanticClaim diagnostic)
    (ay_cvig_RecomputeObligation currentCnf recompute)
    (ay_cvig_diagnostic_no_claim
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_cvig_diagnostic_recompute
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_cvig_unchecked_vivification_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cvig_DiagnosticClauseVivificationGuard
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cvig_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_cvig_diagnostic_no_claim
    currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_cvig_unchecked_vivification_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleSourceClauseManifest : Prop) (unitPropagationReplayMismatch : Prop)
    (removedLiteralCoverageMismatch : Prop)
    (strengthenedClauseLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cvig_DiagnosticClauseVivificationGuard
      currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cvig_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_cvig_diagnostic_recompute
    currentCnf staleSourceClauseManifest unitPropagationReplayMismatch removedLiteralCoverageMismatch strengthenedClauseLedgerGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
