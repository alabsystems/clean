-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cardinality-constraint-detection preprocessing guard soundness.
-- The propositions stand for formula digests, detected-cardinality ledgers,
-- CNF explanation witnesses, rewrite/annotation ledgers, model/proof
-- reconstruction, fallback/build/validator gates, audit transcripts,
-- diagnostics, and public SAT/UNSAT reports.

def ay_cardg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cardg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_cardg_Equisat (original : Prop) (annotated : Prop) :=
  ay_cardg_Conj (original -> annotated) (annotated -> original)

def ay_cardg_Sat (cnf : Prop) (model : Prop) :=
  ay_cardg_Conj cnf model

def ay_cardg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_cardg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_cardg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_cardg_DetectedCardinalityLedger
    (detectedCardinalityLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop) :=
  ay_cardg_Conj detectionCoverage
    (detectedCardinalityLedger -> detectionAccepted)

def ay_cardg_CnfExplanationWitness
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop) :=
  ay_cardg_Conj explanationCoverage
    (explanationWitness -> explanationAccepted)

def ay_cardg_RewriteAnnotationLedger
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop) :=
  ay_cardg_Conj annotationCoverage
    (rewriteAnnotationLedger -> rewriteAccepted)

def ay_cardg_ModelReconstructionWitness
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop) :=
  ay_cardg_Sat annotatedCnf annotatedModel ->
    ay_cardg_Sat originalCnf originalModel

def ay_cardg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (annotatedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cardg_Replay annotatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_cardg_ReconstructionWitnesses
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_cardg_Conj
    (ay_cardg_ModelReconstructionWitness
      annotatedCnf originalCnf annotatedModel originalModel)
    (ay_cardg_UnsatProofReconstructionWitness
      originalCnf annotatedCnf certificate conflict)

def ay_cardg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_cardg_Conj baselineSolver baselineAvailable

def ay_cardg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_cardg_Conj binaryFingerprint buildReproducible

def ay_cardg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_cardg_Conj validatorAccepted validatorVersion

def ay_cardg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_cardg_Conj auditAppended auditAppendOnly

def ay_cardg_AcceptedCardinalityDetectionGuard
    (originalCnf : Prop) (annotatedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedCardinalityLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop)
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop)
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_cardg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_cardg_DetectedCardinalityLedger
       detectedCardinalityLedger detectionAccepted detectionCoverage ->
     ay_cardg_CnfExplanationWitness
       explanationWitness explanationAccepted explanationCoverage ->
     ay_cardg_RewriteAnnotationLedger
       rewriteAnnotationLedger rewriteAccepted annotationCoverage ->
     ay_cardg_ReconstructionWitnesses
       annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
     ay_cardg_Equisat originalCnf annotatedCnf ->
     ay_cardg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_cardg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_cardg_ValidatorGate validatorAccepted validatorVersion ->
     ay_cardg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_cardg_CardinalityDetectionGuardFailure
    (digestMismatch : Prop) (detectionMismatch : Prop)
    (explanationMismatch : Prop) (rewriteMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (detectionMismatch -> result) ->
    (explanationMismatch -> result) ->
    (rewriteMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cardg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_cardg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_cardg_Conj currentCnf recompute

def ay_cardg_DiagnosticCardinalityDetectionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (detectionMismatch : Prop)
    (explanationMismatch : Prop) (rewriteMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_cardg_Conj
    (ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch)
    (ay_cardg_Conj
      (ay_cardg_RecomputeObligation currentCnf recompute)
      (ay_cardg_NoSemanticClaim diagnostic))

def ay_cardg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_cardg_Conj exitCode claim

def ay_cardg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_cardg_Disj
    (ay_cardg_ExitCodeSound exitCode (ay_cardg_Sat originalCnf model))
    (ay_cardg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_cardg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_cardg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_cardg_conj_left
    (left : Prop) (right : Prop) :
    ay_cardg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_cardg_conj_right
    (left : Prop) (right : Prop) :
    ay_cardg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_cardg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_cardg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_cardg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_cardg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_cardg_equisat_forward
    (original : Prop) (annotated : Prop) :
    ay_cardg_Equisat original annotated -> original -> annotated := by
  intro eqsat
  exact ay_cardg_conj_left (original -> annotated) (annotated -> original) eqsat

theorem ay_cardg_equisat_backward
    (original : Prop) (annotated : Prop) :
    ay_cardg_Equisat original annotated -> annotated -> original := by
  intro eqsat
  exact ay_cardg_conj_right (original -> annotated) (annotated -> original) eqsat

theorem ay_cardg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_cardg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_cardg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_cardg_detected_cardinality_ledger_applies
    (detectedCardinalityLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop) :
    ay_cardg_DetectedCardinalityLedger
      detectedCardinalityLedger detectionAccepted detectionCoverage ->
    detectedCardinalityLedger -> detectionAccepted := by
  intro ledger
  exact ay_cardg_conj_right
    detectionCoverage (detectedCardinalityLedger -> detectionAccepted) ledger

theorem ay_cardg_cnf_explanation_witness_applies
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop) :
    ay_cardg_CnfExplanationWitness
      explanationWitness explanationAccepted explanationCoverage ->
    explanationWitness -> explanationAccepted := by
  intro witness
  exact ay_cardg_conj_right
    explanationCoverage (explanationWitness -> explanationAccepted) witness

theorem ay_cardg_rewrite_annotation_ledger_applies
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop) :
    ay_cardg_RewriteAnnotationLedger
      rewriteAnnotationLedger rewriteAccepted annotationCoverage ->
    rewriteAnnotationLedger -> rewriteAccepted := by
  intro ledger
  exact ay_cardg_conj_right
    annotationCoverage (rewriteAnnotationLedger -> rewriteAccepted) ledger

theorem ay_cardg_model_reconstruction
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cardg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_cardg_Sat annotatedCnf annotatedModel ->
    ay_cardg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_cardg_conj_left
    (ay_cardg_ModelReconstructionWitness
      annotatedCnf originalCnf annotatedModel originalModel)
    (ay_cardg_UnsatProofReconstructionWitness
      originalCnf annotatedCnf certificate conflict)
    witnesses

theorem ay_cardg_unsat_proof_reconstruction
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cardg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_cardg_Replay annotatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_cardg_conj_right
    (ay_cardg_ModelReconstructionWitness
      annotatedCnf originalCnf annotatedModel originalModel)
    (ay_cardg_UnsatProofReconstructionWitness
      originalCnf annotatedCnf certificate conflict)
    witnesses

theorem ay_cardg_accepted_equisat
    (originalCnf : Prop) (annotatedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedCardinalityLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop)
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop)
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cardg_AcceptedCardinalityDetectionGuard
      originalCnf annotatedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      detectedCardinalityLedger detectionAccepted detectionCoverage
      explanationWitness explanationAccepted explanationCoverage
      rewriteAnnotationLedger rewriteAccepted annotationCoverage
      annotatedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cardg_Equisat originalCnf annotatedCnf := by
  intro accepted
  exact accepted (ay_cardg_Equisat originalCnf annotatedCnf)
    (fun _digestOk _detectionOk _explanationOk _rewriteOk _reconstruct
      eqsat _fallback _build _validator _audit => eqsat)

theorem ay_cardg_accepted_reconstruction
    (originalCnf : Prop) (annotatedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedCardinalityLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop)
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop)
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_cardg_AcceptedCardinalityDetectionGuard
      originalCnf annotatedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      detectedCardinalityLedger detectionAccepted detectionCoverage
      explanationWitness explanationAccepted explanationCoverage
      rewriteAnnotationLedger rewriteAccepted annotationCoverage
      annotatedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_cardg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_cardg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict)
    (fun _digestOk _detectionOk _explanationOk _rewriteOk reconstruct _eqsat
      _fallback _build _validator _audit => reconstruct)

theorem ay_cardg_sat_pullback
    (originalCnf : Prop) (annotatedCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cardg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_cardg_Sat annotatedCnf annotatedModel ->
    ay_cardg_Sat originalCnf originalModel := by
  intro witnesses satAnnotated
  exact ay_cardg_model_reconstruction
    annotatedCnf originalCnf annotatedModel originalModel
    certificate conflict witnesses satAnnotated

theorem ay_cardg_unsat_pushback
    (originalCnf : Prop) (annotatedCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_cardg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_cardg_Replay annotatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_cardg_unsat_proof_reconstruction
    annotatedCnf originalCnf annotatedModel originalModel
    certificate conflict witnesses replay

theorem ay_cardg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cardg_ExitCodeSound exitCode (ay_cardg_Sat originalCnf originalModel) ->
    ay_cardg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_cardg_disj_left
    (ay_cardg_ExitCodeSound exitCode (ay_cardg_Sat originalCnf originalModel))
    (ay_cardg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_cardg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cardg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_cardg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_cardg_disj_right
    (ay_cardg_ExitCodeSound exitCode (ay_cardg_Sat originalCnf originalModel))
    (ay_cardg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_cardg_failure_digest
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    digestMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result digest_case _detection_case _explanation_case _rewrite_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_cardg_failure_detection
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    detectionMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case detection_case _explanation_case _rewrite_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact detection_case h

theorem ay_cardg_failure_explanation
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    explanationMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case explanation_case _rewrite_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact explanation_case h

theorem ay_cardg_failure_rewrite
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    rewriteMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case rewrite_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact rewrite_case h

theorem ay_cardg_failure_reconstruction
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_cardg_failure_baseline
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    baselineMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _reconstruction_case baseline_case _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_cardg_failure_build
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _reconstruction_case _baseline_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_cardg_failure_validator
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _reconstruction_case _baseline_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_cardg_failure_audit
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_cardg_CardinalityDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _reconstruction_case _baseline_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_cardg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cardg_DiagnosticCardinalityDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_cardg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_cardg_conj_right
    (ay_cardg_RecomputeObligation currentCnf recompute)
    (ay_cardg_NoSemanticClaim diagnostic)
    (ay_cardg_conj_right
      (ay_cardg_CardinalityDetectionGuardFailure
        digestMismatch detectionMismatch explanationMismatch rewriteMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_cardg_Conj
        (ay_cardg_RecomputeObligation currentCnf recompute)
        (ay_cardg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cardg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_cardg_DiagnosticCardinalityDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_cardg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_cardg_conj_left
    (ay_cardg_RecomputeObligation currentCnf recompute)
    (ay_cardg_NoSemanticClaim diagnostic)
    (ay_cardg_conj_right
      (ay_cardg_CardinalityDetectionGuardFailure
        digestMismatch detectionMismatch explanationMismatch rewriteMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_cardg_Conj
        (ay_cardg_RecomputeObligation currentCnf recompute)
        (ay_cardg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_cardg_failed_detection_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_cardg_DiagnosticCardinalityDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_cardg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_cardg_Conj
      (ay_cardg_NoSemanticClaim diagnostic)
      (ay_cardg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_cardg_conj_intro
    (ay_cardg_NoSemanticClaim diagnostic)
    (ay_cardg_RecomputeObligation currentCnf recompute)
    (ay_cardg_diagnostic_no_claim
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)
    (ay_cardg_diagnostic_recompute
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_cardg_failed_detection_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_cardg_DiagnosticCardinalityDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_cardg_ExitCodeSound exitCode (ay_cardg_Sat originalCnf model) ->
    ay_cardg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_cardg_diagnostic_no_claim
    currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard

theorem ay_cardg_failed_detection_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_cardg_DiagnosticCardinalityDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_cardg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_cardg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_cardg_diagnostic_no_claim
    currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard
