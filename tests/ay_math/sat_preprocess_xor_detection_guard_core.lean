-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- XOR-detection preprocessing guard soundness.
-- The propositions stand for formula digests, detected-XOR ledgers,
-- CNF-to-XOR explanation witnesses, rewrite/annotation ledgers, model/proof
-- reconstruction, fallback/build/validator gates, audit transcripts,
-- diagnostics, and public SAT/UNSAT reports.

def ay_xdgg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_xdgg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_xdgg_Equisat (original : Prop) (annotated : Prop) :=
  ay_xdgg_Conj (original -> annotated) (annotated -> original)

def ay_xdgg_Sat (cnf : Prop) (model : Prop) :=
  ay_xdgg_Conj cnf model

def ay_xdgg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_xdgg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_xdgg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_xdgg_DetectedXorLedger
    (detectedXorLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop) :=
  ay_xdgg_Conj detectionCoverage
    (detectedXorLedger -> detectionAccepted)

def ay_xdgg_CnfToXorExplanationWitness
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop) :=
  ay_xdgg_Conj explanationCoverage
    (explanationWitness -> explanationAccepted)

def ay_xdgg_RewriteAnnotationLedger
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop) :=
  ay_xdgg_Conj annotationCoverage
    (rewriteAnnotationLedger -> rewriteAccepted)

def ay_xdgg_ModelLiftWitness
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop) :=
  ay_xdgg_Sat annotatedCnf annotatedModel ->
    ay_xdgg_Sat originalCnf originalModel

def ay_xdgg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (annotatedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_xdgg_Replay annotatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_xdgg_ReconstructionWitnesses
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_xdgg_Conj
    (ay_xdgg_ModelLiftWitness
      annotatedCnf originalCnf annotatedModel originalModel)
    (ay_xdgg_UnsatProofReconstructionWitness
      originalCnf annotatedCnf certificate conflict)

def ay_xdgg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_xdgg_Conj baselineSolver baselineAvailable

def ay_xdgg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_xdgg_Conj binaryFingerprint buildReproducible

def ay_xdgg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_xdgg_Conj validatorAccepted validatorVersion

def ay_xdgg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_xdgg_Conj auditAppended auditAppendOnly

def ay_xdgg_AcceptedXorDetectionGuard
    (originalCnf : Prop) (annotatedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedXorLedger : Prop) (detectionAccepted : Prop)
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
    (ay_xdgg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_xdgg_DetectedXorLedger
       detectedXorLedger detectionAccepted detectionCoverage ->
     ay_xdgg_CnfToXorExplanationWitness
       explanationWitness explanationAccepted explanationCoverage ->
     ay_xdgg_RewriteAnnotationLedger
       rewriteAnnotationLedger rewriteAccepted annotationCoverage ->
     ay_xdgg_ReconstructionWitnesses
       annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
     ay_xdgg_Equisat originalCnf annotatedCnf ->
     ay_xdgg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_xdgg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_xdgg_ValidatorGate validatorAccepted validatorVersion ->
     ay_xdgg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_xdgg_XorDetectionGuardFailure
    (digestMismatch : Prop) (detectionMismatch : Prop)
    (explanationMismatch : Prop) (rewriteMismatch : Prop)
    (liftMismatch : Prop) (reconstructionMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (detectionMismatch -> result) ->
    (explanationMismatch -> result) ->
    (rewriteMismatch -> result) ->
    (liftMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_xdgg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_xdgg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_xdgg_Conj currentCnf recompute

def ay_xdgg_DiagnosticXorDetectionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (detectionMismatch : Prop)
    (explanationMismatch : Prop) (rewriteMismatch : Prop)
    (liftMismatch : Prop) (reconstructionMismatch : Prop)
    (baselineMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_xdgg_Conj
    (ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_xdgg_Conj
      (ay_xdgg_RecomputeObligation currentCnf recompute)
      (ay_xdgg_NoSemanticClaim diagnostic))

def ay_xdgg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_xdgg_Conj exitCode claim

def ay_xdgg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_xdgg_Disj
    (ay_xdgg_ExitCodeSound exitCode (ay_xdgg_Sat originalCnf model))
    (ay_xdgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_xdgg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_xdgg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_xdgg_conj_left
    (left : Prop) (right : Prop) :
    ay_xdgg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_xdgg_conj_right
    (left : Prop) (right : Prop) :
    ay_xdgg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_xdgg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_xdgg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_xdgg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_xdgg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_xdgg_equisat_forward
    (original : Prop) (annotated : Prop) :
    ay_xdgg_Equisat original annotated -> original -> annotated := by
  intro eqsat
  exact ay_xdgg_conj_left (original -> annotated) (annotated -> original) eqsat

theorem ay_xdgg_equisat_backward
    (original : Prop) (annotated : Prop) :
    ay_xdgg_Equisat original annotated -> annotated -> original := by
  intro eqsat
  exact ay_xdgg_conj_right (original -> annotated) (annotated -> original) eqsat

theorem ay_xdgg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_xdgg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_xdgg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_xdgg_detected_xor_ledger_applies
    (detectedXorLedger : Prop) (detectionAccepted : Prop)
    (detectionCoverage : Prop) :
    ay_xdgg_DetectedXorLedger
      detectedXorLedger detectionAccepted detectionCoverage ->
    detectedXorLedger -> detectionAccepted := by
  intro ledger
  exact ay_xdgg_conj_right
    detectionCoverage (detectedXorLedger -> detectionAccepted) ledger

theorem ay_xdgg_cnf_to_xor_explanation_applies
    (explanationWitness : Prop) (explanationAccepted : Prop)
    (explanationCoverage : Prop) :
    ay_xdgg_CnfToXorExplanationWitness
      explanationWitness explanationAccepted explanationCoverage ->
    explanationWitness -> explanationAccepted := by
  intro witness
  exact ay_xdgg_conj_right
    explanationCoverage (explanationWitness -> explanationAccepted) witness

theorem ay_xdgg_rewrite_annotation_ledger_applies
    (rewriteAnnotationLedger : Prop) (rewriteAccepted : Prop)
    (annotationCoverage : Prop) :
    ay_xdgg_RewriteAnnotationLedger
      rewriteAnnotationLedger rewriteAccepted annotationCoverage ->
    rewriteAnnotationLedger -> rewriteAccepted := by
  intro ledger
  exact ay_xdgg_conj_right
    annotationCoverage (rewriteAnnotationLedger -> rewriteAccepted) ledger

theorem ay_xdgg_model_lift
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xdgg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_xdgg_Sat annotatedCnf annotatedModel ->
    ay_xdgg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_xdgg_conj_left
    (ay_xdgg_ModelLiftWitness
      annotatedCnf originalCnf annotatedModel originalModel)
    (ay_xdgg_UnsatProofReconstructionWitness
      originalCnf annotatedCnf certificate conflict)
    witnesses

theorem ay_xdgg_unsat_proof_reconstruction
    (annotatedCnf : Prop) (originalCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xdgg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_xdgg_Replay annotatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_xdgg_conj_right
    (ay_xdgg_ModelLiftWitness
      annotatedCnf originalCnf annotatedModel originalModel)
    (ay_xdgg_UnsatProofReconstructionWitness
      originalCnf annotatedCnf certificate conflict)
    witnesses

theorem ay_xdgg_accepted_equisat
    (originalCnf : Prop) (annotatedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedXorLedger : Prop) (detectionAccepted : Prop)
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
    ay_xdgg_AcceptedXorDetectionGuard
      originalCnf annotatedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      detectedXorLedger detectionAccepted detectionCoverage
      explanationWitness explanationAccepted explanationCoverage
      rewriteAnnotationLedger rewriteAccepted annotationCoverage
      annotatedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xdgg_Equisat originalCnf annotatedCnf := by
  intro accepted
  exact accepted (ay_xdgg_Equisat originalCnf annotatedCnf)
    (fun _digestOk _detectionOk _explanationOk _rewriteOk
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_xdgg_accepted_reconstruction
    (originalCnf : Prop) (annotatedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedXorLedger : Prop) (detectionAccepted : Prop)
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
    ay_xdgg_AcceptedXorDetectionGuard
      originalCnf annotatedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      detectedXorLedger detectionAccepted detectionCoverage
      explanationWitness explanationAccepted explanationCoverage
      rewriteAnnotationLedger rewriteAccepted annotationCoverage
      annotatedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_xdgg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_xdgg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict)
    (fun _digestOk _detectionOk _explanationOk _rewriteOk reconstruct
      _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_xdgg_sat_pullback
    (originalCnf : Prop) (annotatedCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xdgg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_xdgg_Sat annotatedCnf annotatedModel ->
    ay_xdgg_Sat originalCnf originalModel := by
  intro witnesses satAnnotated
  exact ay_xdgg_model_lift
    annotatedCnf originalCnf annotatedModel originalModel
    certificate conflict witnesses satAnnotated

theorem ay_xdgg_unsat_pushback
    (originalCnf : Prop) (annotatedCnf : Prop)
    (annotatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_xdgg_ReconstructionWitnesses
      annotatedCnf originalCnf annotatedModel originalModel certificate conflict ->
    ay_xdgg_Replay annotatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_xdgg_unsat_proof_reconstruction
    annotatedCnf originalCnf annotatedModel originalModel
    certificate conflict witnesses replay

theorem ay_xdgg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_xdgg_ExitCodeSound exitCode (ay_xdgg_Sat originalCnf originalModel) ->
    ay_xdgg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_xdgg_disj_left
    (ay_xdgg_ExitCodeSound exitCode (ay_xdgg_Sat originalCnf originalModel))
    (ay_xdgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_xdgg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_xdgg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_xdgg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_xdgg_disj_right
    (ay_xdgg_ExitCodeSound exitCode (ay_xdgg_Sat originalCnf originalModel))
    (ay_xdgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_xdgg_failure_digest
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result digest_case _detection_case _explanation_case _rewrite_case
    _lift_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact digest_case h

theorem ay_xdgg_failure_detection
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    detectionMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case detection_case _explanation_case _rewrite_case
    _lift_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact detection_case h

theorem ay_xdgg_failure_explanation
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    explanationMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case explanation_case _rewrite_case
    _lift_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact explanation_case h

theorem ay_xdgg_failure_rewrite
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    rewriteMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case rewrite_case
    _lift_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact rewrite_case h

theorem ay_xdgg_failure_lift
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    liftMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    lift_case _reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact lift_case h

theorem ay_xdgg_failure_reconstruction
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _lift_case reconstruction_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case h

theorem ay_xdgg_failure_baseline
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _lift_case _reconstruction_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case h

theorem ay_xdgg_failure_build
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _lift_case _reconstruction_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case h

theorem ay_xdgg_failure_validator
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _lift_case _reconstruction_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case h

theorem ay_xdgg_failure_audit
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_xdgg_XorDetectionGuardFailure
      digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _digest_case _detection_case _explanation_case _rewrite_case
    _lift_case _reconstruction_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case h

theorem ay_xdgg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_xdgg_DiagnosticXorDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_xdgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_xdgg_conj_right
    (ay_xdgg_RecomputeObligation currentCnf recompute)
    (ay_xdgg_NoSemanticClaim diagnostic)
    (ay_xdgg_conj_right
      (ay_xdgg_XorDetectionGuardFailure
        digestMismatch detectionMismatch explanationMismatch rewriteMismatch
        liftMismatch reconstructionMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_xdgg_Conj
        (ay_xdgg_RecomputeObligation currentCnf recompute)
        (ay_xdgg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_xdgg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_xdgg_DiagnosticXorDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_xdgg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_xdgg_conj_left
    (ay_xdgg_RecomputeObligation currentCnf recompute)
    (ay_xdgg_NoSemanticClaim diagnostic)
    (ay_xdgg_conj_right
      (ay_xdgg_XorDetectionGuardFailure
        digestMismatch detectionMismatch explanationMismatch rewriteMismatch
        liftMismatch reconstructionMismatch baselineMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_xdgg_Conj
        (ay_xdgg_RecomputeObligation currentCnf recompute)
        (ay_xdgg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_xdgg_failed_xor_detection_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_xdgg_DiagnosticXorDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_xdgg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_xdgg_Conj
      (ay_xdgg_NoSemanticClaim diagnostic)
      (ay_xdgg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_xdgg_conj_intro
    (ay_xdgg_NoSemanticClaim diagnostic)
    (ay_xdgg_RecomputeObligation currentCnf recompute)
    (ay_xdgg_diagnostic_no_claim
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_xdgg_diagnostic_recompute
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_xdgg_failed_xor_detection_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_xdgg_DiagnosticXorDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_xdgg_ExitCodeSound exitCode (ay_xdgg_Sat originalCnf model) ->
    ay_xdgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_xdgg_diagnostic_no_claim
    currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
    liftMismatch reconstructionMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_xdgg_failed_xor_detection_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch detectionMismatch explanationMismatch rewriteMismatch : Prop)
    (liftMismatch reconstructionMismatch baselineMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_xdgg_DiagnosticXorDetectionGuard
      currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
      liftMismatch reconstructionMismatch baselineMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_xdgg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_xdgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_xdgg_diagnostic_no_claim
    currentCnf digestMismatch detectionMismatch explanationMismatch rewriteMismatch
    liftMismatch reconstructionMismatch baselineMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
