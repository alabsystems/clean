-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Component-decomposition guard soundness.
-- The propositions stand for component partition manifests, variable-disjointness witnesses, clause coverage
-- digests, per-component fingerprint ledgers, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_cdcg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cdcg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cdcg_Equisat (before : Prop) (after : Prop) :=
  ay_cdcg_Conj (before -> after) (after -> before)

def ay_cdcg_Sat (cnf : Prop) (model : Prop) :=
  ay_cdcg_Conj cnf model

def ay_cdcg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cdcg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_cdcg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_cdcg_ComponentPartitionManifest
    (componentPartition : Prop) (partitionAccepted : Prop)
    (componentPartitionManifest : Prop) :=
  ay_cdcg_Conj componentPartitionManifest (componentPartition -> partitionAccepted)

def ay_cdcg_VariableDisjointnessWitness
    (componentVariables : Prop) (variableDisjoint : Prop)
    (variableDisjointnessWitness : Prop) :=
  ay_cdcg_Conj variableDisjointnessWitness (componentVariables -> variableDisjoint)

def ay_cdcg_ClauseCoverageDigest
    (clauseSet : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageWitness : Prop) :=
  ay_cdcg_Conj clauseCoverageWitness (clauseSet -> clauseCoverageAccepted)

def ay_cdcg_PerComponentFingerprintLedger
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop) :=
  ay_cdcg_Conj componentFingerprintLedger (componentFingerprint -> fingerprintRecorded)

def ay_cdcg_ModelMergeReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_cdcg_Sat replayedCnf replayedModel ->
    ay_cdcg_Sat originalCnf originalModel

def ay_cdcg_ProofMergeReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cdcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cdcg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cdcg_Conj
    (ay_cdcg_ModelMergeReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cdcg_ProofMergeReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_cdcg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_cdcg_Conj fingerprintWitness
    (ay_cdcg_IdMatch originalFingerprint replayedFingerprint)

def ay_cdcg_CheckerReplay
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_cdcg_Conj decompositionReplayCertificate checkerAccepted

def ay_cdcg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cdcg_Conj baselineSolver baselineAvailable

def ay_cdcg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cdcg_Conj binaryFingerprint buildReproducible

def ay_cdcg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cdcg_Conj validatorAccepted validatorVersion

def ay_cdcg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cdcg_Conj auditAppended auditAppendOnly

def ay_cdcg_AcceptedComponentDecompositionGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (componentPartition : Prop) (partitionAccepted : Prop) (componentPartitionManifest : Prop)
    (componentVariables : Prop) (variableDisjoint : Prop) (variableDisjointnessWitness : Prop)
    (clauseSet : Prop) (clauseCoverageAccepted : Prop) (clauseCoverageWitness : Prop)
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cdcg_ComponentPartitionManifest
       componentPartition partitionAccepted componentPartitionManifest ->
     ay_cdcg_VariableDisjointnessWitness
       componentVariables variableDisjoint variableDisjointnessWitness ->
     ay_cdcg_ClauseCoverageDigest
       clauseSet clauseCoverageAccepted clauseCoverageWitness ->
     ay_cdcg_PerComponentFingerprintLedger
       componentFingerprint fingerprintRecorded componentFingerprintLedger ->
     ay_cdcg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_cdcg_Equisat originalCnf replayedCnf ->
     ay_cdcg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_cdcg_CheckerReplay decompositionReplayCertificate checkerAccepted ->
     ay_cdcg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cdcg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cdcg_ValidatorGate validatorAccepted validatorVersion ->
     ay_cdcg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cdcg_ComponentDecompositionGuardFailure
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleComponentPartitionManifest -> result) ->
    (variableDisjointnessMismatch -> result) ->
    (clauseCoverageMismatch -> result) ->
    (componentFingerprintLedgerGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_cdcg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cdcg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cdcg_Conj currentCnf recompute

def ay_cdcg_DiagnosticComponentDecompositionGuard
    (currentCnf : Prop)
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cdcg_Conj
    (ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_cdcg_Conj
      (ay_cdcg_RecomputeObligation currentCnf recompute)
      (ay_cdcg_NoSemanticClaim diagnostic))

def ay_cdcg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cdcg_Conj exitCode claim

def ay_cdcg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cdcg_Disj
    (ay_cdcg_ExitCodeSound exitCode (ay_cdcg_Sat originalCnf model))
    (ay_cdcg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cdcg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cdcg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cdcg_conj_left
    (left : Prop) (right : Prop) :
    ay_cdcg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cdcg_conj_right
    (left : Prop) (right : Prop) :
    ay_cdcg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cdcg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cdcg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cdcg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cdcg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cdcg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_cdcg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_cdcg_conj_left (before -> after) (after -> before) eqsat

theorem ay_cdcg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_cdcg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_cdcg_conj_right (before -> after) (after -> before) eqsat

theorem ay_cdcg_component_partition_manifest_applies
    (componentPartition : Prop) (partitionAccepted : Prop)
    (componentPartitionManifest : Prop) :
    ay_cdcg_ComponentPartitionManifest
      componentPartition partitionAccepted componentPartitionManifest ->
    componentPartition -> partitionAccepted := by
  intro digest
  exact ay_cdcg_conj_right componentPartitionManifest
    (componentPartition -> partitionAccepted) digest

theorem ay_cdcg_variable_disjointness_witness_applies
    (componentVariables : Prop) (variableDisjoint : Prop)
    (variableDisjointnessWitness : Prop) :
    ay_cdcg_VariableDisjointnessWitness
      componentVariables variableDisjoint variableDisjointnessWitness ->
    componentVariables -> variableDisjoint := by
  intro digest
  exact ay_cdcg_conj_right variableDisjointnessWitness
    (componentVariables -> variableDisjoint) digest

theorem ay_cdcg_clause_coverage_digest_applies
    (clauseSet : Prop) (clauseCoverageAccepted : Prop)
    (clauseCoverageWitness : Prop) :
    ay_cdcg_ClauseCoverageDigest
      clauseSet clauseCoverageAccepted clauseCoverageWitness ->
    clauseSet -> clauseCoverageAccepted := by
  intro ledger
  exact ay_cdcg_conj_right clauseCoverageWitness
    (clauseSet -> clauseCoverageAccepted) ledger

theorem ay_cdcg_per_component_fingerprint_ledger_applies
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop) :
    ay_cdcg_PerComponentFingerprintLedger
      componentFingerprint fingerprintRecorded componentFingerprintLedger ->
    componentFingerprint -> fingerprintRecorded := by
  intro coverage
  exact ay_cdcg_conj_right componentFingerprintLedger
    (componentFingerprint -> fingerprintRecorded) coverage

theorem ay_cdcg_model_merge_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cdcg_ModelMergeReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_cdcg_conj_left
    (ay_cdcg_ModelMergeReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cdcg_ProofMergeReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cdcg_proof_merge_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_cdcg_ProofMergeReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_cdcg_conj_right
    (ay_cdcg_ModelMergeReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_cdcg_ProofMergeReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_cdcg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (componentPartition : Prop) (partitionAccepted : Prop) (componentPartitionManifest : Prop)
    (componentVariables : Prop) (variableDisjoint : Prop) (variableDisjointnessWitness : Prop)
    (clauseSet : Prop) (clauseCoverageAccepted : Prop) (clauseCoverageWitness : Prop)
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cdcg_AcceptedComponentDecompositionGuard
      originalCnf replayedCnf
      componentPartition partitionAccepted componentPartitionManifest
      componentVariables variableDisjoint variableDisjointnessWitness
      clauseSet clauseCoverageAccepted clauseCoverageWitness
      componentFingerprint fingerprintRecorded componentFingerprintLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      decompositionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cdcg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_cdcg_Equisat originalCnf replayedCnf)
    (fun _manifest _disjoint _coverage _fingerprint _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_cdcg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (componentPartition : Prop) (partitionAccepted : Prop) (componentPartitionManifest : Prop)
    (componentVariables : Prop) (variableDisjoint : Prop) (variableDisjointnessWitness : Prop)
    (clauseSet : Prop) (clauseCoverageAccepted : Prop) (clauseCoverageWitness : Prop)
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cdcg_AcceptedComponentDecompositionGuard
      originalCnf replayedCnf
      componentPartition partitionAccepted componentPartitionManifest
      componentVariables variableDisjoint variableDisjointnessWitness
      clauseSet clauseCoverageAccepted clauseCoverageWitness
      componentFingerprint fingerprintRecorded componentFingerprintLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      decompositionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cdcg_CheckerReplay decompositionReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_cdcg_CheckerReplay decompositionReplayCertificate checkerAccepted)
    (fun _manifest _disjoint _coverage _fingerprint _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_cdcg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (componentPartition : Prop) (partitionAccepted : Prop) (componentPartitionManifest : Prop)
    (componentVariables : Prop) (variableDisjoint : Prop) (variableDisjointnessWitness : Prop)
    (clauseSet : Prop) (clauseCoverageAccepted : Prop) (clauseCoverageWitness : Prop)
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cdcg_AcceptedComponentDecompositionGuard
      originalCnf replayedCnf
      componentPartition partitionAccepted componentPartitionManifest
      componentVariables variableDisjoint variableDisjointnessWitness
      clauseSet clauseCoverageAccepted clauseCoverageWitness
      componentFingerprint fingerprintRecorded componentFingerprintLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      decompositionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cdcg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_cdcg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _disjoint _coverage _fingerprint _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_cdcg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_cdcg_ModelMergeReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_cdcg_Sat replayedCnf replayedModel ->
    ay_cdcg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_cdcg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cdcg_ProofMergeReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_cdcg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_cdcg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (componentPartition : Prop) (partitionAccepted : Prop) (componentPartitionManifest : Prop)
    (componentVariables : Prop) (variableDisjoint : Prop) (variableDisjointnessWitness : Prop)
    (clauseSet : Prop) (clauseCoverageAccepted : Prop) (clauseCoverageWitness : Prop)
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cdcg_AcceptedComponentDecompositionGuard
      originalCnf replayedCnf
      componentPartition partitionAccepted componentPartitionManifest
      componentVariables variableDisjoint variableDisjointnessWitness
      clauseSet clauseCoverageAccepted clauseCoverageWitness
      componentFingerprint fingerprintRecorded componentFingerprintLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      decompositionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cdcg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_cdcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_cdcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _disjoint _coverage _fingerprint reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_cdcg_disj_left
        (ay_cdcg_ExitCodeSound exitCode
          (ay_cdcg_Sat originalCnf originalModel))
        (ay_cdcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cdcg_conj_intro exitCode
          (ay_cdcg_Sat originalCnf originalModel)
          hexit
          ((ay_cdcg_model_merge_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_cdcg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (componentPartition : Prop) (partitionAccepted : Prop) (componentPartitionManifest : Prop)
    (componentVariables : Prop) (variableDisjoint : Prop) (variableDisjointnessWitness : Prop)
    (clauseSet : Prop) (clauseCoverageAccepted : Prop) (clauseCoverageWitness : Prop)
    (componentFingerprint : Prop) (fingerprintRecorded : Prop)
    (componentFingerprintLedger : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (decompositionReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_cdcg_AcceptedComponentDecompositionGuard
      originalCnf replayedCnf
      componentPartition partitionAccepted componentPartitionManifest
      componentVariables variableDisjoint variableDisjointnessWitness
      clauseSet clauseCoverageAccepted clauseCoverageWitness
      componentFingerprint fingerprintRecorded componentFingerprintLedger
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      decompositionReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cdcg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_cdcg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_cdcg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _disjoint _coverage _fingerprint reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_cdcg_disj_right
        (ay_cdcg_ExitCodeSound exitCode
          (ay_cdcg_Sat originalCnf originalModel))
        (ay_cdcg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_cdcg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_cdcg_proof_merge_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_cdcg_failure_stale_component_partition_manifest
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleComponentPartitionManifest ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result partition_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case _build_case
    _validator_case _audit_case
  exact partition_case failure

theorem ay_cdcg_failure_variable_disjointness
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    variableDisjointnessMismatch ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case disjoint_case _coverage_case _fingerprint_case
    _reconstruction_case _fingerprint_case _disjoint_case _baseline_case
    _build_case _validator_case _audit_case
  exact disjoint_case failure

theorem ay_cdcg_failure_clause_coverage_digest
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    clauseCoverageMismatch ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_cdcg_failure_per_component_fingerprint_ledger
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    componentFingerprintLedgerGap ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case coverage_case _reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_cdcg_failure_reconstruction
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_cdcg_failure_stale_fingerprint
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    fingerprint_case _disjoint_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_cdcg_failure_unchecked_replay
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case disjoint_case _baseline_case _build_case
    _validator_case _audit_case
  exact disjoint_case failure

theorem ay_cdcg_failure_missing_baseline
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case _disjoint_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_cdcg_failure_build
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_cdcg_failure_validator
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_cdcg_failure_audit
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_cdcg_ComponentDecompositionGuardFailure
      staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _disjoint_case _coverage_case _fingerprint_case _reconstruction_case
    _fingerprint_case _disjoint_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_cdcg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticComponentDecompositionGuard
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cdcg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_cdcg_conj_right
    (ay_cdcg_RecomputeObligation currentCnf recompute)
    (ay_cdcg_NoSemanticClaim diagnostic)
    (ay_cdcg_conj_right
      (ay_cdcg_ComponentDecompositionGuardFailure
        staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cdcg_Conj
        (ay_cdcg_RecomputeObligation currentCnf recompute)
        (ay_cdcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cdcg_diagnostic_recompute
    (currentCnf : Prop)
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cdcg_DiagnosticComponentDecompositionGuard
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cdcg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_cdcg_conj_left
    (ay_cdcg_RecomputeObligation currentCnf recompute)
    (ay_cdcg_NoSemanticClaim diagnostic)
    (ay_cdcg_conj_right
      (ay_cdcg_ComponentDecompositionGuardFailure
        staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_cdcg_Conj
        (ay_cdcg_RecomputeObligation currentCnf recompute)
        (ay_cdcg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_cdcg_unchecked_decomposition_cannot_bless_public_result
    (currentCnf : Prop)
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cdcg_DiagnosticComponentDecompositionGuard
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cdcg_Conj
      (ay_cdcg_NoSemanticClaim diagnostic)
      (ay_cdcg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_cdcg_conj_intro
    (ay_cdcg_NoSemanticClaim diagnostic)
    (ay_cdcg_RecomputeObligation currentCnf recompute)
    (ay_cdcg_diagnostic_no_claim
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_cdcg_diagnostic_recompute
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_cdcg_unchecked_decomposition_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cdcg_DiagnosticComponentDecompositionGuard
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cdcg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_cdcg_diagnostic_no_claim
    currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_cdcg_unchecked_decomposition_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleComponentPartitionManifest : Prop) (variableDisjointnessMismatch : Prop)
    (clauseCoverageMismatch : Prop)
    (componentFingerprintLedgerGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_cdcg_DiagnosticComponentDecompositionGuard
      currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_cdcg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_cdcg_diagnostic_recompute
    currentCnf staleComponentPartitionManifest variableDisjointnessMismatch clauseCoverageMismatch componentFingerprintLedgerGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
