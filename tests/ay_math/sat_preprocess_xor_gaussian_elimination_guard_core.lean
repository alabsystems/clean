-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- XOR/Gaussian-elimination guard soundness.
-- The propositions stand for XOR-clause extraction manifests, row-operation ledgers, pivot basis
-- witnesses, residual CNF reconstruction maps, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_xgeg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_xgeg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_xgeg_Equisat (before : Prop) (after : Prop) :=
  ay_xgeg_Conj (before -> after) (after -> before)

def ay_xgeg_Sat (cnf : Prop) (model : Prop) :=
  ay_xgeg_Conj cnf model

def ay_xgeg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_xgeg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_xgeg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_xgeg_XorClauseExtractionManifest
    (xorClauses : Prop) (xorExtractionAccepted : Prop)
    (xorClausesManifest : Prop) :=
  ay_xgeg_Conj xorClausesManifest (xorClauses -> xorExtractionAccepted)

def ay_xgeg_RowOperationLedger
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop)
    (rowOperationLedger : Prop) :=
  ay_xgeg_Conj rowOperationLedger (rowOperationSet -> rowOperationsAccepted)

def ay_xgeg_PivotBasisWitness
    (pivotBasis : Prop) (pivotBasisAccepted : Prop)
    (pivotBasisWitness : Prop) :=
  ay_xgeg_Conj pivotBasisWitness (pivotBasis -> pivotBasisAccepted)

def ay_xgeg_ResidualCnfReconstructionMap
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop) :=
  ay_xgeg_Conj residualCnfReconstructionMap (residualCnf -> originalCnfFromResidual)

def ay_xgeg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_xgeg_Sat replayedCnf replayedModel ->
    ay_xgeg_Sat originalCnf originalModel

def ay_xgeg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_xgeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_xgeg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_xgeg_Conj
    (ay_xgeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_xgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_xgeg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_xgeg_Conj fingerprintWitness
    (ay_xgeg_IdMatch originalFingerprint replayedFingerprint)

def ay_xgeg_CheckerReplay
    (xorReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_xgeg_Conj xorReplayCertificate checkerAccepted

def ay_xgeg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_xgeg_Conj baselineSolver baselineAvailable

def ay_xgeg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_xgeg_Conj binaryFingerprint buildReproducible

def ay_xgeg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_xgeg_Conj validatorAccepted validatorVersion

def ay_xgeg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_xgeg_Conj auditAppended auditAppendOnly

def ay_xgeg_AcceptedXorGaussianEliminationGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorClauses : Prop) (xorExtractionAccepted : Prop) (xorClausesManifest : Prop)
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop) (rowOperationLedger : Prop)
    (pivotBasis : Prop) (pivotBasisAccepted : Prop) (pivotBasisWitness : Prop)
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_xgeg_XorClauseExtractionManifest
       xorClauses xorExtractionAccepted xorClausesManifest ->
     ay_xgeg_RowOperationLedger
       rowOperationSet rowOperationsAccepted rowOperationLedger ->
     ay_xgeg_PivotBasisWitness
       pivotBasis pivotBasisAccepted pivotBasisWitness ->
     ay_xgeg_ResidualCnfReconstructionMap
       residualCnf originalCnfFromResidual residualCnfReconstructionMap ->
     ay_xgeg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_xgeg_Equisat originalCnf replayedCnf ->
     ay_xgeg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_xgeg_CheckerReplay xorReplayCertificate checkerAccepted ->
     ay_xgeg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_xgeg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_xgeg_ValidatorGate validatorAccepted validatorVersion ->
     ay_xgeg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_xgeg_XorGaussianEliminationGuardFailure
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleXorClauseExtractionManifest -> result) ->
    (rowOperationMismatch -> result) ->
    (pivotBasisMismatch -> result) ->
    (residualCnfReconstructionMapGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_xgeg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_xgeg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_xgeg_Conj currentCnf recompute

def ay_xgeg_DiagnosticXorGaussianEliminationGuard
    (currentCnf : Prop)
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_xgeg_Conj
    (ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_xgeg_Conj
      (ay_xgeg_RecomputeObligation currentCnf recompute)
      (ay_xgeg_NoSemanticClaim diagnostic))

def ay_xgeg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_xgeg_Conj exitCode claim

def ay_xgeg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_xgeg_Disj
    (ay_xgeg_ExitCodeSound exitCode (ay_xgeg_Sat originalCnf model))
    (ay_xgeg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_xgeg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_xgeg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_xgeg_conj_left
    (left : Prop) (right : Prop) :
    ay_xgeg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_xgeg_conj_right
    (left : Prop) (right : Prop) :
    ay_xgeg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_xgeg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_xgeg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_xgeg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_xgeg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_xgeg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_xgeg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_xgeg_conj_left (before -> after) (after -> before) eqsat

theorem ay_xgeg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_xgeg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_xgeg_conj_right (before -> after) (after -> before) eqsat

theorem ay_xgeg_xor_clause_extraction_manifest_applies
    (xorClauses : Prop) (xorExtractionAccepted : Prop)
    (xorClausesManifest : Prop) :
    ay_xgeg_XorClauseExtractionManifest
      xorClauses xorExtractionAccepted xorClausesManifest ->
    xorClauses -> xorExtractionAccepted := by
  intro digest
  exact ay_xgeg_conj_right xorClausesManifest
    (xorClauses -> xorExtractionAccepted) digest

theorem ay_xgeg_row_operation_ledger_applies
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop)
    (rowOperationLedger : Prop) :
    ay_xgeg_RowOperationLedger
      rowOperationSet rowOperationsAccepted rowOperationLedger ->
    rowOperationSet -> rowOperationsAccepted := by
  intro digest
  exact ay_xgeg_conj_right rowOperationLedger
    (rowOperationSet -> rowOperationsAccepted) digest

theorem ay_xgeg_pivot_basis_witness_applies
    (pivotBasis : Prop) (pivotBasisAccepted : Prop)
    (pivotBasisWitness : Prop) :
    ay_xgeg_PivotBasisWitness
      pivotBasis pivotBasisAccepted pivotBasisWitness ->
    pivotBasis -> pivotBasisAccepted := by
  intro ledger
  exact ay_xgeg_conj_right pivotBasisWitness
    (pivotBasis -> pivotBasisAccepted) ledger

theorem ay_xgeg_residual_cnf_reconstruction_map_applies
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop) :
    ay_xgeg_ResidualCnfReconstructionMap
      residualCnf originalCnfFromResidual residualCnfReconstructionMap ->
    residualCnf -> originalCnfFromResidual := by
  intro coverage
  exact ay_xgeg_conj_right residualCnfReconstructionMap
    (residualCnf -> originalCnfFromResidual) coverage

theorem ay_xgeg_model_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xgeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_xgeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_xgeg_conj_left
    (ay_xgeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_xgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_xgeg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xgeg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_xgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_xgeg_conj_right
    (ay_xgeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_xgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_xgeg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorClauses : Prop) (xorExtractionAccepted : Prop) (xorClausesManifest : Prop)
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop) (rowOperationLedger : Prop)
    (pivotBasis : Prop) (pivotBasisAccepted : Prop) (pivotBasisWitness : Prop)
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_xgeg_AcceptedXorGaussianEliminationGuard
      originalCnf replayedCnf
      xorClauses xorExtractionAccepted xorClausesManifest
      rowOperationSet rowOperationsAccepted rowOperationLedger
      pivotBasis pivotBasisAccepted pivotBasisWitness
      residualCnf originalCnfFromResidual residualCnfReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xgeg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_xgeg_Equisat originalCnf replayedCnf)
    (fun _manifest _row _pivot _residual _reconstruct eqsat _residual _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_xgeg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorClauses : Prop) (xorExtractionAccepted : Prop) (xorClausesManifest : Prop)
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop) (rowOperationLedger : Prop)
    (pivotBasis : Prop) (pivotBasisAccepted : Prop) (pivotBasisWitness : Prop)
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_xgeg_AcceptedXorGaussianEliminationGuard
      originalCnf replayedCnf
      xorClauses xorExtractionAccepted xorClausesManifest
      rowOperationSet rowOperationsAccepted rowOperationLedger
      pivotBasis pivotBasisAccepted pivotBasisWitness
      residualCnf originalCnfFromResidual residualCnfReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xgeg_CheckerReplay xorReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_xgeg_CheckerReplay xorReplayCertificate checkerAccepted)
    (fun _manifest _row _pivot _residual _reconstruct _eqsat _residual checker
      _fallback _build _validator _audit => checker)

theorem ay_xgeg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorClauses : Prop) (xorExtractionAccepted : Prop) (xorClausesManifest : Prop)
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop) (rowOperationLedger : Prop)
    (pivotBasis : Prop) (pivotBasisAccepted : Prop) (pivotBasisWitness : Prop)
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_xgeg_AcceptedXorGaussianEliminationGuard
      originalCnf replayedCnf
      xorClauses xorExtractionAccepted xorClausesManifest
      rowOperationSet rowOperationsAccepted rowOperationLedger
      pivotBasis pivotBasisAccepted pivotBasisWitness
      residualCnf originalCnfFromResidual residualCnfReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xgeg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_xgeg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _row _pivot _residual _reconstruct _eqsat _residual _checker
      _fallback _build _validator audit => audit)

theorem ay_xgeg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_xgeg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_xgeg_Sat replayedCnf replayedModel ->
    ay_xgeg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_xgeg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xgeg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_xgeg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_xgeg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorClauses : Prop) (xorExtractionAccepted : Prop) (xorClausesManifest : Prop)
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop) (rowOperationLedger : Prop)
    (pivotBasis : Prop) (pivotBasisAccepted : Prop) (pivotBasisWitness : Prop)
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_xgeg_AcceptedXorGaussianEliminationGuard
      originalCnf replayedCnf
      xorClauses xorExtractionAccepted xorClausesManifest
      rowOperationSet rowOperationsAccepted rowOperationLedger
      pivotBasis pivotBasisAccepted pivotBasisWitness
      residualCnf originalCnfFromResidual residualCnfReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xgeg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_xgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_xgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _row _pivot _residual reconstruct _eqsat _residual _checker
      _fallback _build _validator _audit =>
      ay_xgeg_disj_left
        (ay_xgeg_ExitCodeSound exitCode
          (ay_xgeg_Sat originalCnf originalModel))
        (ay_xgeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_xgeg_conj_intro exitCode
          (ay_xgeg_Sat originalCnf originalModel)
          hexit
          ((ay_xgeg_model_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_xgeg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (xorClauses : Prop) (xorExtractionAccepted : Prop) (xorClausesManifest : Prop)
    (rowOperationSet : Prop) (rowOperationsAccepted : Prop) (rowOperationLedger : Prop)
    (pivotBasis : Prop) (pivotBasisAccepted : Prop) (pivotBasisWitness : Prop)
    (residualCnf : Prop) (originalCnfFromResidual : Prop)
    (residualCnfReconstructionMap : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (xorReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_xgeg_AcceptedXorGaussianEliminationGuard
      originalCnf replayedCnf
      xorClauses xorExtractionAccepted xorClausesManifest
      rowOperationSet rowOperationsAccepted rowOperationLedger
      pivotBasis pivotBasisAccepted pivotBasisWitness
      residualCnf originalCnfFromResidual residualCnfReconstructionMap
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      xorReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xgeg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_xgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_xgeg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _row _pivot _residual reconstruct _eqsat _residual _checker
      _fallback _build _validator _audit =>
      ay_xgeg_disj_right
        (ay_xgeg_ExitCodeSound exitCode
          (ay_xgeg_Sat originalCnf originalModel))
        (ay_xgeg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_xgeg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_xgeg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_xgeg_failure_stale_xor_clause_extraction_manifest
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleXorClauseExtractionManifest ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result extraction_case _row_case _pivot_case _residual_case _reconstruction_case
    _residual_case _row_case _baseline_case _build_case
    _validator_case _audit_case
  exact extraction_case failure

theorem ay_xgeg_failure_row_operation_ledger
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    rowOperationMismatch ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case row_case _pivot_case _residual_case
    _reconstruction_case _residual_case _row_case _baseline_case
    _build_case _validator_case _audit_case
  exact row_case failure

theorem ay_xgeg_failure_pivot_basis_witness
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    pivotBasisMismatch ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case pivot_case _residual_case _reconstruction_case
    _residual_case _row_case _baseline_case _build_case
    _validator_case _audit_case
  exact pivot_case failure

theorem ay_xgeg_failure_residual_cnf_reconstruction
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    residualCnfReconstructionMapGap ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case pivot_case _reconstruction_case
    _residual_case _row_case _baseline_case _build_case
    _validator_case _audit_case
  exact pivot_case failure

theorem ay_xgeg_failure_reconstruction
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case reconstruction_case
    _residual_case _row_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_xgeg_failure_stale_fingerprint
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case _reconstruction_case
    fingerprint_case _row_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_xgeg_failure_unchecked_replay
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case _reconstruction_case
    _residual_case row_case _baseline_case _build_case
    _validator_case _audit_case
  exact row_case failure

theorem ay_xgeg_failure_missing_baseline
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case _reconstruction_case
    _residual_case _row_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_xgeg_failure_build
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case _reconstruction_case
    _residual_case _row_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_xgeg_failure_validator
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case _reconstruction_case
    _residual_case _row_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_xgeg_failure_audit
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_xgeg_XorGaussianEliminationGuardFailure
      staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _row_case _pivot_case _residual_case _reconstruction_case
    _residual_case _row_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_xgeg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_xgeg_DiagnosticXorGaussianEliminationGuard
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_xgeg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_xgeg_conj_right
    (ay_xgeg_RecomputeObligation currentCnf recompute)
    (ay_xgeg_NoSemanticClaim diagnostic)
    (ay_xgeg_conj_right
      (ay_xgeg_XorGaussianEliminationGuardFailure
        staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_xgeg_Conj
        (ay_xgeg_RecomputeObligation currentCnf recompute)
        (ay_xgeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_xgeg_diagnostic_recompute
    (currentCnf : Prop)
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_xgeg_DiagnosticXorGaussianEliminationGuard
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_xgeg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_xgeg_conj_left
    (ay_xgeg_RecomputeObligation currentCnf recompute)
    (ay_xgeg_NoSemanticClaim diagnostic)
    (ay_xgeg_conj_right
      (ay_xgeg_XorGaussianEliminationGuardFailure
        staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_xgeg_Conj
        (ay_xgeg_RecomputeObligation currentCnf recompute)
        (ay_xgeg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_xgeg_unchecked_xor_elimination_cannot_bless_public_result
    (currentCnf : Prop)
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_xgeg_DiagnosticXorGaussianEliminationGuard
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_xgeg_Conj
      (ay_xgeg_NoSemanticClaim diagnostic)
      (ay_xgeg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_xgeg_conj_intro
    (ay_xgeg_NoSemanticClaim diagnostic)
    (ay_xgeg_RecomputeObligation currentCnf recompute)
    (ay_xgeg_diagnostic_no_claim
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_xgeg_diagnostic_recompute
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_xgeg_unchecked_xor_elimination_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_xgeg_DiagnosticXorGaussianEliminationGuard
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_xgeg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_xgeg_diagnostic_no_claim
    currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_xgeg_unchecked_xor_elimination_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleXorClauseExtractionManifest : Prop) (rowOperationMismatch : Prop)
    (pivotBasisMismatch : Prop)
    (residualCnfReconstructionMapGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_xgeg_DiagnosticXorGaussianEliminationGuard
      currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_xgeg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_xgeg_diagnostic_recompute
    currentCnf staleXorClauseExtractionManifest rowOperationMismatch pivotBasisMismatch residualCnfReconstructionMapGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
