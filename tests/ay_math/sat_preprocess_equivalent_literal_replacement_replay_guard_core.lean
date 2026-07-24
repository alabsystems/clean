-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalent-literal replacement replay guard soundness.
-- The propositions stand for equivalence-class witness ledgers, representative maps, replacement
-- coverage, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_elrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_elrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_elrg_Equisat (before : Prop) (after : Prop) :=
  ay_elrg_Conj (before -> after) (after -> before)

def ay_elrg_Sat (cnf : Prop) (model : Prop) :=
  ay_elrg_Conj cnf model

def ay_elrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_elrg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_elrg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_elrg_EquivalenceClassWitnessLedger
    (equivalentLiteral : Prop) (equivalenceWitness : Prop)
    (equivalenceLedger : Prop) :=
  ay_elrg_Conj equivalenceLedger (equivalentLiteral -> equivalenceWitness)

def ay_elrg_RepresentativeMap
    (equivalentLiteral : Prop) (representativeLiteral : Prop)
    (representativeMapWitness : Prop) :=
  ay_elrg_Conj representativeMapWitness
    (equivalentLiteral -> representativeLiteral)

def ay_elrg_ReplacementCoverage
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop) :=
  ay_elrg_Conj replacementCoverageWitness (replacedLiteral -> coveredReplacement)

def ay_elrg_ModelReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_elrg_Sat replayedCnf replayedModel ->
    ay_elrg_Sat originalCnf originalModel

def ay_elrg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_elrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_elrg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_elrg_Conj
    (ay_elrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_elrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_elrg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_elrg_Conj fingerprintWitness
    (ay_elrg_IdMatch originalFingerprint replayedFingerprint)

def ay_elrg_CheckerReplay
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_elrg_Conj replacementReplayCertificate checkerAccepted

def ay_elrg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_elrg_Conj baselineSolver baselineAvailable

def ay_elrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_elrg_Conj binaryFingerprint buildReproducible

def ay_elrg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_elrg_Conj validatorAccepted validatorVersion

def ay_elrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_elrg_Conj auditAppended auditAppendOnly

def ay_elrg_AcceptedEquivalentLiteralReplacementReplayGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalentLiteral : Prop) (equivalenceWitness : Prop) (equivalenceLedger : Prop)
    (representativeLiteral : Prop) (representativeMapWitness : Prop)
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_elrg_EquivalenceClassWitnessLedger
       equivalentLiteral equivalenceWitness equivalenceLedger ->
     ay_elrg_RepresentativeMap
       equivalentLiteral representativeLiteral representativeMapWitness ->
     ay_elrg_ReplacementCoverage
       replacedLiteral coveredReplacement replacementCoverageWitness ->
     ay_elrg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_elrg_Equisat originalCnf replayedCnf ->
     ay_elrg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_elrg_CheckerReplay replacementReplayCertificate checkerAccepted ->
     ay_elrg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_elrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_elrg_ValidatorGate validatorAccepted validatorVersion ->
     ay_elrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (missingEquivalenceWitness -> result) ->
    (representativeMapMismatch -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_elrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_elrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_elrg_Conj currentCnf recompute

def ay_elrg_DiagnosticEquivalentLiteralReplacementReplayGuard
    (currentCnf : Prop)
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_elrg_Conj
    (ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure auditContradiction)
    (ay_elrg_Conj
      (ay_elrg_RecomputeObligation currentCnf recompute)
      (ay_elrg_NoSemanticClaim diagnostic))

def ay_elrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_elrg_Conj exitCode claim

def ay_elrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_elrg_Disj
    (ay_elrg_ExitCodeSound exitCode (ay_elrg_Sat originalCnf model))
    (ay_elrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_elrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_elrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_elrg_conj_left
    (left : Prop) (right : Prop) :
    ay_elrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_elrg_conj_right
    (left : Prop) (right : Prop) :
    ay_elrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_elrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_elrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_elrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_elrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_elrg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_elrg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_elrg_conj_left (before -> after) (after -> before) eqsat

theorem ay_elrg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_elrg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_elrg_conj_right (before -> after) (after -> before) eqsat

theorem ay_elrg_equivalence_witness_applies
    (equivalentLiteral : Prop) (equivalenceWitness : Prop)
    (equivalenceLedger : Prop) :
    ay_elrg_EquivalenceClassWitnessLedger
      equivalentLiteral equivalenceWitness equivalenceLedger ->
    equivalentLiteral -> equivalenceWitness := by
  intro ledger
  exact ay_elrg_conj_right equivalenceLedger
    (equivalentLiteral -> equivalenceWitness) ledger

theorem ay_elrg_representative_map_applies
    (equivalentLiteral : Prop) (representativeLiteral : Prop)
    (representativeMapWitness : Prop) :
    ay_elrg_RepresentativeMap
      equivalentLiteral representativeLiteral representativeMapWitness ->
    equivalentLiteral -> representativeLiteral := by
  intro representativeMap
  exact ay_elrg_conj_right representativeMapWitness
    (equivalentLiteral -> representativeLiteral) representativeMap

theorem ay_elrg_replacement_coverage
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop) :
    ay_elrg_ReplacementCoverage
      replacedLiteral coveredReplacement replacementCoverageWitness ->
    replacedLiteral -> coveredReplacement := by
  intro coverage
  exact ay_elrg_conj_right replacementCoverageWitness
    (replacedLiteral -> coveredReplacement) coverage

theorem ay_elrg_reconstruction_model
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_elrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_elrg_conj_left
    (ay_elrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_elrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_elrg_reconstruction_proof
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elrg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_elrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_elrg_conj_right
    (ay_elrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_elrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_elrg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalentLiteral : Prop) (equivalenceWitness : Prop) (equivalenceLedger : Prop)
    (representativeLiteral : Prop) (representativeMapWitness : Prop)
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_elrg_AcceptedEquivalentLiteralReplacementReplayGuard
      originalCnf replayedCnf
      equivalentLiteral equivalenceWitness equivalenceLedger
      representativeLiteral representativeMapWitness
      replacedLiteral coveredReplacement replacementCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      replacementReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elrg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_elrg_Equisat originalCnf replayedCnf)
    (fun _equivalence _representativeMap _coverage _reconstruct eqsat _fingerprint _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_elrg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalentLiteral : Prop) (equivalenceWitness : Prop) (equivalenceLedger : Prop)
    (representativeLiteral : Prop) (representativeMapWitness : Prop)
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_elrg_AcceptedEquivalentLiteralReplacementReplayGuard
      originalCnf replayedCnf
      equivalentLiteral equivalenceWitness equivalenceLedger
      representativeLiteral representativeMapWitness
      replacedLiteral coveredReplacement replacementCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      replacementReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elrg_CheckerReplay replacementReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_elrg_CheckerReplay replacementReplayCertificate checkerAccepted)
    (fun _equivalence _representativeMap _coverage _reconstruct _eqsat _fingerprint checker
      _fallback _build _validator _audit => checker)

theorem ay_elrg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalentLiteral : Prop) (equivalenceWitness : Prop) (equivalenceLedger : Prop)
    (representativeLiteral : Prop) (representativeMapWitness : Prop)
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_elrg_AcceptedEquivalentLiteralReplacementReplayGuard
      originalCnf replayedCnf
      equivalentLiteral equivalenceWitness equivalenceLedger
      representativeLiteral representativeMapWitness
      replacedLiteral coveredReplacement replacementCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      replacementReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elrg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_elrg_AuditTranscript auditAppended auditAppendOnly)
    (fun _equivalence _representativeMap _coverage _reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator audit => audit)

theorem ay_elrg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_elrg_ModelReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_elrg_Sat replayedCnf replayedModel ->
    ay_elrg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_elrg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_elrg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_elrg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_elrg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalentLiteral : Prop) (equivalenceWitness : Prop) (equivalenceLedger : Prop)
    (representativeLiteral : Prop) (representativeMapWitness : Prop)
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_elrg_AcceptedEquivalentLiteralReplacementReplayGuard
      originalCnf replayedCnf
      equivalentLiteral equivalenceWitness equivalenceLedger
      representativeLiteral representativeMapWitness
      replacedLiteral coveredReplacement replacementCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      replacementReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elrg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_elrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_elrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _equivalence _representativeMap _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_elrg_disj_left
        (ay_elrg_ExitCodeSound exitCode
          (ay_elrg_Sat originalCnf originalModel))
        (ay_elrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_elrg_conj_intro exitCode
          (ay_elrg_Sat originalCnf originalModel)
          hexit
          ((ay_elrg_reconstruction_model
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_elrg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (equivalentLiteral : Prop) (equivalenceWitness : Prop) (equivalenceLedger : Prop)
    (representativeLiteral : Prop) (representativeMapWitness : Prop)
    (replacedLiteral : Prop) (coveredReplacement : Prop)
    (replacementCoverageWitness : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (replacementReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_elrg_AcceptedEquivalentLiteralReplacementReplayGuard
      originalCnf replayedCnf
      equivalentLiteral equivalenceWitness equivalenceLedger
      representativeLiteral representativeMapWitness
      replacedLiteral coveredReplacement replacementCoverageWitness
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      replacementReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_elrg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_elrg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_elrg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _equivalence _representativeMap _coverage reconstruct _eqsat _fingerprint _checker
      _fallback _build _validator _audit =>
      ay_elrg_disj_right
        (ay_elrg_ExitCodeSound exitCode
          (ay_elrg_Sat originalCnf originalModel))
        (ay_elrg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_elrg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_elrg_reconstruction_proof
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_elrg_failure_missing_equivalence_witness
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingEquivalenceWitness ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact witness_case failure

theorem ay_elrg_failure_representative_map
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    representativeMapMismatch ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case representative_case _coverage_case
    _reconstruction_case _fingerprint_case _replay_case _baseline_case
    _build_case _validator_case _audit_case
  exact representative_case failure

theorem ay_elrg_failure_coverage
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    coverageGap ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact coverage_case failure

theorem ay_elrg_failure_reconstruction
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_elrg_failure_stale_fingerprint
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    fingerprint_case _replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_elrg_failure_unchecked_replay
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case replay_case _baseline_case _build_case
    _validator_case _audit_case
  exact replay_case failure

theorem ay_elrg_failure_missing_baseline
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_elrg_failure_build
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_elrg_failure_validator
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_elrg_failure_audit
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
      missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _witness_case _representative_case _coverage_case _reconstruction_case
    _fingerprint_case _replay_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_elrg_diagnostic_no_claim
    (currentCnf : Prop)
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_elrg_DiagnosticEquivalentLiteralReplacementReplayGuard
      currentCnf missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_elrg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_elrg_conj_right
    (ay_elrg_RecomputeObligation currentCnf recompute)
    (ay_elrg_NoSemanticClaim diagnostic)
    (ay_elrg_conj_right
      (ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
        missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_elrg_Conj
        (ay_elrg_RecomputeObligation currentCnf recompute)
        (ay_elrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_elrg_diagnostic_recompute
    (currentCnf : Prop)
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_elrg_DiagnosticEquivalentLiteralReplacementReplayGuard
      currentCnf missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_elrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_elrg_conj_left
    (ay_elrg_RecomputeObligation currentCnf recompute)
    (ay_elrg_NoSemanticClaim diagnostic)
    (ay_elrg_conj_right
      (ay_elrg_EquivalentLiteralReplacementReplayGuardFailure
        missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_elrg_Conj
        (ay_elrg_RecomputeObligation currentCnf recompute)
        (ay_elrg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_elrg_unchecked_replacement_cannot_bless_public_result
    (currentCnf : Prop)
    (missingEquivalenceWitness : Prop) (representativeMapMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_elrg_DiagnosticEquivalentLiteralReplacementReplayGuard
      currentCnf missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_elrg_Conj
      (ay_elrg_NoSemanticClaim diagnostic)
      (ay_elrg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_elrg_conj_intro
    (ay_elrg_NoSemanticClaim diagnostic)
    (ay_elrg_RecomputeObligation currentCnf recompute)
    (ay_elrg_diagnostic_no_claim
      currentCnf missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_elrg_diagnostic_recompute
      currentCnf missingEquivalenceWitness representativeMapMismatch coverageGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
