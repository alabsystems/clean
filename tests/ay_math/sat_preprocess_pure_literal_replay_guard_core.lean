-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Pure-literal elimination replay guard soundness.
-- The propositions stand for pure-literal witness ledgers, removed-clause coverage, assignment-extension
-- witnesses, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_plrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_plrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_plrg_Equisat (before : Prop) (after : Prop) :=
  ay_plrg_Conj (before -> after) (after -> before)

def ay_plrg_Sat (cnf : Prop) (model : Prop) :=
  ay_plrg_Conj cnf model

def ay_plrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_plrg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_plrg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_plrg_PureLiteralWitnessLedger
    (pureLiteral : Prop) (purityWitness : Prop)
    (purityLedger : Prop) :=
  ay_plrg_Conj purityLedger (pureLiteral -> purityWitness)

def ay_plrg_RemovedClauseCoverage
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop) :=
  ay_plrg_Conj removalCoverageWitness (removedClause -> coveredRemovedClause)

def ay_plrg_AssignmentExtensionWitnessLedger
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop) :=
  ay_plrg_Conj extensionLedger (reducedAssignment -> extendedAssignment)

def ay_plrg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_plrg_Sat replayedCnf replayedModel ->
    ay_plrg_Sat originalCnf originalModel

def ay_plrg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_plrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_plrg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_plrg_Conj
    (ay_plrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_plrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_plrg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_plrg_Conj fingerprintWitness
    (ay_plrg_IdMatch originalFingerprint replayedFingerprint)

def ay_plrg_CheckerReplay
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_plrg_Conj pureLiteralReplayCertificate checkerAccepted

def ay_plrg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_plrg_Conj baselineSolver baselineAvailable

def ay_plrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_plrg_Conj binaryFingerprint buildReproducible

def ay_plrg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_plrg_Conj validatorAccepted validatorVersion

def ay_plrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_plrg_Conj auditAppended auditAppendOnly

def ay_plrg_AcceptedPureLiteralReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (pureLiteral : Prop) (purityWitness : Prop) (purityLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_plrg_PureLiteralWitnessLedger
       pureLiteral purityWitness purityLedger ->
     ay_plrg_RemovedClauseCoverage
       removedClause coveredRemovedClause removalCoverageWitness ->
     ay_plrg_AssignmentExtensionWitnessLedger
       reducedAssignment extendedAssignment extensionLedger ->
     ay_plrg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_plrg_Equisat originalCnf replayedCnf ->
     ay_plrg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_plrg_CheckerReplay pureLiteralReplayCertificate checkerAccepted ->
     ay_plrg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_plrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_plrg_ValidatorGate validatorAccepted validatorVersion ->
     ay_plrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_plrg_PureLiteralReplayGuardFailure
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (missingPurityWitness -> result) ->
    (coverageGap -> result) ->
    (assignmentExtensionMismatch -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_plrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_plrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_plrg_Conj currentCnf recompute

def ay_plrg_DiagnosticPureLiteralReplayGuard
    (currentCnf : Prop)
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_plrg_Conj
    (ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_plrg_Conj
      (ay_plrg_RecomputeObligation currentCnf recompute)
      (ay_plrg_NoSemanticClaim diagnostic))

def ay_plrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_plrg_Conj exitCode claim

def ay_plrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_plrg_Disj
    (ay_plrg_ExitCodeSound exitCode (ay_plrg_Sat originalCnf model))
    (ay_plrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_plrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_plrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_plrg_conj_left
    (left : Prop) (right : Prop) :
    ay_plrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_plrg_conj_right
    (left : Prop) (right : Prop) :
    ay_plrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_plrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_plrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_plrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_plrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_plrg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_plrg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_plrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_plrg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_plrg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_plrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_plrg_pure_literal_witness_applies
    (pureLiteral : Prop) (purityWitness : Prop)
    (purityLedger : Prop) :
    ay_plrg_PureLiteralWitnessLedger
      pureLiteral purityWitness purityLedger ->
    pureLiteral -> purityWitness := by
  intro ledger
  exact ay_plrg_conj_right purityLedger
    (pureLiteral -> purityWitness) ledger

theorem ay_plrg_removed_clause_coverage
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop) :
    ay_plrg_RemovedClauseCoverage
      removedClause coveredRemovedClause removalCoverageWitness ->
    removedClause -> coveredRemovedClause := by
  intro coverage
  exact ay_plrg_conj_right removalCoverageWitness
    (removedClause -> coveredRemovedClause) coverage

theorem ay_plrg_assignment_extension_applies
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop) :
    ay_plrg_AssignmentExtensionWitnessLedger
      reducedAssignment extendedAssignment extensionLedger ->
    reducedAssignment -> extendedAssignment := by
  intro extension
  exact ay_plrg_conj_right extensionLedger
    (reducedAssignment -> extendedAssignment) extension

theorem ay_plrg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_plrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_plrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_plrg_conj_left
    (ay_plrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_plrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_plrg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_plrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_plrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_plrg_conj_right
    (ay_plrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_plrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_plrg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (pureLiteral : Prop) (purityWitness : Prop) (purityLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_plrg_AcceptedPureLiteralReplayGuard
      originalCnf replayedCnf
      pureLiteral purityWitness purityLedger
      removedClause coveredRemovedClause removalCoverageWitness
      reducedAssignment extendedAssignment extensionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pureLiteralReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_plrg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_plrg_Equisat originalCnf replayedCnf)
    (fun _purity _coverage _extension _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_plrg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (pureLiteral : Prop) (purityWitness : Prop) (purityLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_plrg_AcceptedPureLiteralReplayGuard
      originalCnf replayedCnf
      pureLiteral purityWitness purityLedger
      removedClause coveredRemovedClause removalCoverageWitness
      reducedAssignment extendedAssignment extensionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pureLiteralReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_plrg_CheckerReplay pureLiteralReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_plrg_CheckerReplay pureLiteralReplayCertificate checkerAccepted)
    (fun _purity _coverage _extension _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_plrg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (pureLiteral : Prop) (purityWitness : Prop) (purityLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_plrg_AcceptedPureLiteralReplayGuard
      originalCnf replayedCnf
      pureLiteral purityWitness purityLedger
      removedClause coveredRemovedClause removalCoverageWitness
      reducedAssignment extendedAssignment extensionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pureLiteralReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_plrg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_plrg_AuditTranscript auditAppended auditAppendOnly)
    (fun _purity _coverage _extension _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_plrg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_plrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_plrg_Sat replayedCnf replayedModel ->
    ay_plrg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_plrg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_plrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_plrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_plrg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (pureLiteral : Prop) (purityWitness : Prop) (purityLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_plrg_AcceptedPureLiteralReplayGuard
      originalCnf replayedCnf
      pureLiteral purityWitness purityLedger
      removedClause coveredRemovedClause removalCoverageWitness
      reducedAssignment extendedAssignment extensionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pureLiteralReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_plrg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_plrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_plrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _purity _coverage _extension reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_plrg_disj_left
        (ay_plrg_ExitCodeSound exitCode
          (ay_plrg_Sat originalCnf originalModel))
        (ay_plrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_plrg_conj_intro exitCode
          (ay_plrg_Sat originalCnf originalModel)
          hexit
          ((ay_plrg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_plrg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (pureLiteral : Prop) (purityWitness : Prop) (purityLedger : Prop)
    (removedClause : Prop) (coveredRemovedClause : Prop)
    (removalCoverageWitness : Prop)
    (reducedAssignment : Prop) (extendedAssignment : Prop)
    (extensionLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (pureLiteralReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_plrg_AcceptedPureLiteralReplayGuard
      originalCnf replayedCnf
      pureLiteral purityWitness purityLedger
      removedClause coveredRemovedClause removalCoverageWitness
      reducedAssignment extendedAssignment extensionLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      pureLiteralReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_plrg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_plrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_plrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _purity _coverage _extension reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_plrg_disj_right
        (ay_plrg_ExitCodeSound exitCode
          (ay_plrg_Sat originalCnf originalModel))
        (ay_plrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_plrg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_plrg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_plrg_failure_missing_purity_witness
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingPurityWitness ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result witness_case _coverage_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_plrg_failure_coverage
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case coverage_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_plrg_failure_assignment_extension
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    assignmentExtensionMismatch ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case extension_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact extension_case failure

theorem ay_plrg_failure_reconstruction
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_plrg_failure_stale_fingerprint
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_plrg_failure_unchecked_replay
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_plrg_failure_missing_baseline
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_plrg_failure_build
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_plrg_failure_validator
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_plrg_failure_audit
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_plrg_PureLiteralReplayGuardFailure
      missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _coverage_case _extension_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_plrg_diagnostic_no_claim
    (currentCnf : Prop)
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_plrg_DiagnosticPureLiteralReplayGuard
      currentCnf missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_plrg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_plrg_conj_right
    (ay_plrg_RecomputeObligation currentCnf recompute)
    (ay_plrg_NoSemanticClaim diagnostic)
    (ay_plrg_conj_right
      (ay_plrg_PureLiteralReplayGuardFailure
        missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_plrg_Conj
        (ay_plrg_RecomputeObligation currentCnf recompute)
        (ay_plrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_plrg_diagnostic_recompute
    (currentCnf : Prop)
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_plrg_DiagnosticPureLiteralReplayGuard
      currentCnf missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_plrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_plrg_conj_left
    (ay_plrg_RecomputeObligation currentCnf recompute)
    (ay_plrg_NoSemanticClaim diagnostic)
    (ay_plrg_conj_right
      (ay_plrg_PureLiteralReplayGuardFailure
        missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_plrg_Conj
        (ay_plrg_RecomputeObligation currentCnf recompute)
        (ay_plrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_plrg_unchecked_pure_literal_cannot_bless_public_result
    (currentCnf : Prop)
    (missingPurityWitness : Prop) (coverageGap : Prop)
    (assignmentExtensionMismatch : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_plrg_DiagnosticPureLiteralReplayGuard
      currentCnf missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_plrg_Conj
      (ay_plrg_NoSemanticClaim diagnostic)
      (ay_plrg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_plrg_conj_intro
    (ay_plrg_NoSemanticClaim diagnostic)
    (ay_plrg_RecomputeObligation currentCnf recompute)
    (ay_plrg_diagnostic_no_claim
      currentCnf missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_plrg_diagnostic_recompute
      currentCnf missingPurityWitness coverageGap assignmentExtensionMismatch reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
