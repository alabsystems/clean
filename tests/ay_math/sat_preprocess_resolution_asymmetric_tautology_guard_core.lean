-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- RAT/asymmetric-tautology preprocessing guard soundness.
-- The propositions stand for formula digests, candidate-clause ledgers,
-- RAT pivot witnesses, asymmetric propagation replay, deletion/addition
-- ledgers, model/proof reconstruction, fallback/build/validator gates, audit
-- transcripts, diagnostics, and public SAT/UNSAT reports.

def ay_ratg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ratg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ratg_Equisat (original : Prop) (transformed : Prop) :=
  ay_ratg_Conj (original -> transformed) (transformed -> original)

def ay_ratg_Sat (cnf : Prop) (model : Prop) :=
  ay_ratg_Conj cnf model

def ay_ratg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ratg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_ratg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_ratg_CandidateClauseLedger
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_ratg_Conj candidateCoverage
    (candidateClauseLedger -> candidateAccepted)

def ay_ratg_RatPivotWitness
    (ratPivotWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop) :=
  ay_ratg_Conj pivotCoverage (ratPivotWitness -> pivotAccepted)

def ay_ratg_AsymmetricPropagationReplay
    (propagationReplay : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop) :=
  ay_ratg_Conj propagationCoverage
    (propagationReplay -> propagationAccepted)

def ay_ratg_DeletionAdditionLedger
    (deletionAdditionLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :=
  ay_ratg_Conj ledgerCoverage (deletionAdditionLedger -> ledgerAccepted)

def ay_ratg_ModelReconstructionWitness
    (transformedCnf : Prop) (originalCnf : Prop)
    (transformedModel : Prop) (originalModel : Prop) :=
  ay_ratg_Sat transformedCnf transformedModel ->
    ay_ratg_Sat originalCnf originalModel

def ay_ratg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (transformedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ratg_Replay transformedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_ratg_ReconstructionWitnesses
    (transformedCnf : Prop) (originalCnf : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ratg_Conj
    (ay_ratg_ModelReconstructionWitness
      transformedCnf originalCnf transformedModel originalModel)
    (ay_ratg_UnsatProofReconstructionWitness
      originalCnf transformedCnf certificate conflict)

def ay_ratg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_ratg_Conj baselineSolver baselineAvailable

def ay_ratg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_ratg_Conj binaryFingerprint buildReproducible

def ay_ratg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_ratg_Conj validatorAccepted validatorVersion

def ay_ratg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_ratg_Conj auditAppended auditAppendOnly

def ay_ratg_AcceptedResolutionAsymmetricTautologyGuard
    (originalCnf : Prop) (transformedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (ratPivotWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (propagationReplay : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop)
    (deletionAdditionLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_ratg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_ratg_CandidateClauseLedger
       candidateClauseLedger candidateAccepted candidateCoverage ->
     ay_ratg_RatPivotWitness
       ratPivotWitness pivotAccepted pivotCoverage ->
     ay_ratg_AsymmetricPropagationReplay
       propagationReplay propagationAccepted propagationCoverage ->
     ay_ratg_DeletionAdditionLedger
       deletionAdditionLedger ledgerAccepted ledgerCoverage ->
     ay_ratg_ReconstructionWitnesses
       transformedCnf originalCnf transformedModel originalModel certificate conflict ->
     ay_ratg_Equisat originalCnf transformedCnf ->
     ay_ratg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_ratg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_ratg_ValidatorGate validatorAccepted validatorVersion ->
     ay_ratg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_ratg_RatGuardFailure
    (digestMismatch : Prop) (candidateMismatch : Prop)
    (pivotMismatch : Prop) (propagationMismatch : Prop)
    (ledgerMismatch : Prop) (reconstructionMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (candidateMismatch -> result) ->
    (pivotMismatch -> result) ->
    (propagationMismatch -> result) ->
    (ledgerMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ratg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ratg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_ratg_Conj currentCnf recompute

def ay_ratg_DiagnosticRatGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (candidateMismatch : Prop)
    (pivotMismatch : Prop) (propagationMismatch : Prop)
    (ledgerMismatch : Prop) (reconstructionMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ratg_Conj
    (ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_ratg_Conj
      (ay_ratg_RecomputeObligation currentCnf recompute)
      (ay_ratg_NoSemanticClaim diagnostic))

def ay_ratg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ratg_Conj exitCode claim

def ay_ratg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ratg_Disj
    (ay_ratg_ExitCodeSound exitCode (ay_ratg_Sat originalCnf model))
    (ay_ratg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_ratg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ratg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ratg_conj_left
    (left : Prop) (right : Prop) :
    ay_ratg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ratg_conj_right
    (left : Prop) (right : Prop) :
    ay_ratg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ratg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ratg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ratg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ratg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ratg_equisat_forward
    (original : Prop) (transformed : Prop) :
    ay_ratg_Equisat original transformed -> original -> transformed := by
  intro eqsat
  exact ay_ratg_conj_left (original -> transformed) (transformed -> original) eqsat

theorem ay_ratg_equisat_backward
    (original : Prop) (transformed : Prop) :
    ay_ratg_Equisat original transformed -> transformed -> original := by
  intro eqsat
  exact ay_ratg_conj_right (original -> transformed) (transformed -> original) eqsat

theorem ay_ratg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_ratg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_ratg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_ratg_candidate_clause_ledger_applies
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_ratg_CandidateClauseLedger
      candidateClauseLedger candidateAccepted candidateCoverage ->
    candidateClauseLedger -> candidateAccepted := by
  intro ledger
  exact ay_ratg_conj_right
    candidateCoverage (candidateClauseLedger -> candidateAccepted) ledger

theorem ay_ratg_rat_pivot_witness_applies
    (ratPivotWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop) :
    ay_ratg_RatPivotWitness ratPivotWitness pivotAccepted pivotCoverage ->
    ratPivotWitness -> pivotAccepted := by
  intro witness
  exact ay_ratg_conj_right
    pivotCoverage (ratPivotWitness -> pivotAccepted) witness

theorem ay_ratg_asymmetric_propagation_replay_applies
    (propagationReplay : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop) :
    ay_ratg_AsymmetricPropagationReplay
      propagationReplay propagationAccepted propagationCoverage ->
    propagationReplay -> propagationAccepted := by
  intro replay
  exact ay_ratg_conj_right
    propagationCoverage (propagationReplay -> propagationAccepted) replay

theorem ay_ratg_deletion_addition_ledger_applies
    (deletionAdditionLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :
    ay_ratg_DeletionAdditionLedger
      deletionAdditionLedger ledgerAccepted ledgerCoverage ->
    deletionAdditionLedger -> ledgerAccepted := by
  intro ledger
  exact ay_ratg_conj_right
    ledgerCoverage (deletionAdditionLedger -> ledgerAccepted) ledger

theorem ay_ratg_model_reconstruction
    (transformedCnf : Prop) (originalCnf : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ratg_ReconstructionWitnesses
      transformedCnf originalCnf transformedModel originalModel certificate conflict ->
    ay_ratg_Sat transformedCnf transformedModel ->
    ay_ratg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_ratg_conj_left
    (ay_ratg_ModelReconstructionWitness
      transformedCnf originalCnf transformedModel originalModel)
    (ay_ratg_UnsatProofReconstructionWitness
      originalCnf transformedCnf certificate conflict)
    witnesses

theorem ay_ratg_unsat_proof_reconstruction
    (transformedCnf : Prop) (originalCnf : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ratg_ReconstructionWitnesses
      transformedCnf originalCnf transformedModel originalModel certificate conflict ->
    ay_ratg_Replay transformedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_ratg_conj_right
    (ay_ratg_ModelReconstructionWitness
      transformedCnf originalCnf transformedModel originalModel)
    (ay_ratg_UnsatProofReconstructionWitness
      originalCnf transformedCnf certificate conflict)
    witnesses

theorem ay_ratg_accepted_equisat
    (originalCnf : Prop) (transformedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (ratPivotWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (propagationReplay : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop)
    (deletionAdditionLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ratg_AcceptedResolutionAsymmetricTautologyGuard
      originalCnf transformedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      candidateClauseLedger candidateAccepted candidateCoverage
      ratPivotWitness pivotAccepted pivotCoverage
      propagationReplay propagationAccepted propagationCoverage
      deletionAdditionLedger ledgerAccepted ledgerCoverage
      transformedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ratg_Equisat originalCnf transformedCnf := by
  intro accepted
  exact accepted (ay_ratg_Equisat originalCnf transformedCnf)
    (fun _digestOk _candidateOk _pivotOk _propagationOk _ledgerOk
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_ratg_accepted_reconstruction
    (originalCnf : Prop) (transformedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (ratPivotWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (propagationReplay : Prop) (propagationAccepted : Prop)
    (propagationCoverage : Prop)
    (deletionAdditionLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ratg_AcceptedResolutionAsymmetricTautologyGuard
      originalCnf transformedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      candidateClauseLedger candidateAccepted candidateCoverage
      ratPivotWitness pivotAccepted pivotCoverage
      propagationReplay propagationAccepted propagationCoverage
      deletionAdditionLedger ledgerAccepted ledgerCoverage
      transformedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_ratg_ReconstructionWitnesses
      transformedCnf originalCnf transformedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_ratg_ReconstructionWitnesses
      transformedCnf originalCnf transformedModel originalModel certificate conflict)
    (fun _digestOk _candidateOk _pivotOk _propagationOk _ledgerOk reconstruct
      _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_ratg_sat_pullback
    (originalCnf : Prop) (transformedCnf : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ratg_ReconstructionWitnesses
      transformedCnf originalCnf transformedModel originalModel certificate conflict ->
    ay_ratg_Sat transformedCnf transformedModel ->
    ay_ratg_Sat originalCnf originalModel := by
  intro witnesses satTransformed
  exact ay_ratg_model_reconstruction
    transformedCnf originalCnf transformedModel originalModel
    certificate conflict witnesses satTransformed

theorem ay_ratg_unsat_pushback
    (originalCnf : Prop) (transformedCnf : Prop)
    (transformedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ratg_ReconstructionWitnesses
      transformedCnf originalCnf transformedModel originalModel certificate conflict ->
    ay_ratg_Replay transformedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_ratg_unsat_proof_reconstruction
    transformedCnf originalCnf transformedModel originalModel
    certificate conflict witnesses replay

theorem ay_ratg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ratg_ExitCodeSound exitCode (ay_ratg_Sat originalCnf originalModel) ->
    ay_ratg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_ratg_disj_left
    (ay_ratg_ExitCodeSound exitCode (ay_ratg_Sat originalCnf originalModel))
    (ay_ratg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_ratg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ratg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ratg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_ratg_disj_right
    (ay_ratg_ExitCodeSound exitCode (ay_ratg_Sat originalCnf originalModel))
    (ay_ratg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_ratg_failure_digest
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result digest_case _candidate_case _pivot_case _propagation_case
    _ledger_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact digest_case h

theorem ay_ratg_failure_candidate
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    candidateMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case candidate_case _pivot_case _propagation_case
    _ledger_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact candidate_case h

theorem ay_ratg_failure_pivot
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    pivotMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case pivot_case _propagation_case
    _ledger_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact pivot_case h

theorem ay_ratg_failure_propagation
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    propagationMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case propagation_case
    _ledger_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact propagation_case h

theorem ay_ratg_failure_ledger
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    ledgerMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case _propagation_case
    ledger_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact ledger_case h

theorem ay_ratg_failure_reconstruction
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case _propagation_case
    _ledger_case reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_ratg_failure_baseline
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case _propagation_case
    _ledger_case _reconstruction_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_ratg_failure_build
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case _propagation_case
    _ledger_case _reconstruction_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_ratg_failure_validator
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case _propagation_case
    _ledger_case _reconstruction_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_ratg_failure_audit
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_ratg_RatGuardFailure
      digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _candidate_case _pivot_case _propagation_case
    _ledger_case _reconstruction_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_ratg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ratg_DiagnosticRatGuard
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ratg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_ratg_conj_right
    (ay_ratg_RecomputeObligation currentCnf recompute)
    (ay_ratg_NoSemanticClaim diagnostic)
    (ay_ratg_conj_right
      (ay_ratg_RatGuardFailure
        digestMismatch candidateMismatch pivotMismatch propagationMismatch
        ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_ratg_Conj
        (ay_ratg_RecomputeObligation currentCnf recompute)
        (ay_ratg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ratg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ratg_DiagnosticRatGuard
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ratg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_ratg_conj_left
    (ay_ratg_RecomputeObligation currentCnf recompute)
    (ay_ratg_NoSemanticClaim diagnostic)
    (ay_ratg_conj_right
      (ay_ratg_RatGuardFailure
        digestMismatch candidateMismatch pivotMismatch propagationMismatch
        ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_ratg_Conj
        (ay_ratg_RecomputeObligation currentCnf recompute)
        (ay_ratg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ratg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ratg_DiagnosticRatGuard
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ratg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_ratg_Conj
      (ay_ratg_NoSemanticClaim diagnostic)
      (ay_ratg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_ratg_conj_intro
    (ay_ratg_NoSemanticClaim diagnostic)
    (ay_ratg_RecomputeObligation currentCnf recompute)
    (ay_ratg_diagnostic_no_claim
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_ratg_diagnostic_recompute
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_ratg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_ratg_DiagnosticRatGuard
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ratg_ExitCodeSound exitCode (ay_ratg_Sat originalCnf model) ->
    ay_ratg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_ratg_diagnostic_no_claim
    currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
    ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_ratg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch candidateMismatch pivotMismatch propagationMismatch : Prop)
    (ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_ratg_DiagnosticRatGuard
      currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
      ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ratg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ratg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_ratg_diagnostic_no_claim
    currentCnf digestMismatch candidateMismatch pivotMismatch propagationMismatch
    ledgerMismatch reconstructionMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
