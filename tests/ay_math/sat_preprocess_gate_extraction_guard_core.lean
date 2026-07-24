-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Gate-extraction preprocessing guard soundness.
-- The propositions stand for formula digests, detected-gate ledgers,
-- definition-introduction ledgers, Tseitin equivalence witnesses, model/proof
-- reconstruction, fallback/build/validator gates, audit transcripts,
-- diagnostics, and public SAT/UNSAT reports.

def ay_gegg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_gegg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_gegg_Equisat (original : Prop) (extracted : Prop) :=
  ay_gegg_Conj (original -> extracted) (extracted -> original)

def ay_gegg_Sat (cnf : Prop) (model : Prop) :=
  ay_gegg_Conj cnf model

def ay_gegg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_gegg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_gegg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_gegg_DetectedGateLedger
    (detectedGateLedger : Prop) (gateAccepted : Prop)
    (gateCoverage : Prop) :=
  ay_gegg_Conj gateCoverage (detectedGateLedger -> gateAccepted)

def ay_gegg_DefinitionIntroductionLedger
    (definitionLedger : Prop) (definitionAccepted : Prop)
    (definitionCoverage : Prop) :=
  ay_gegg_Conj definitionCoverage (definitionLedger -> definitionAccepted)

def ay_gegg_TseitinEquivalenceWitness
    (tseitinWitness : Prop) (tseitinAccepted : Prop)
    (equivalenceCoverage : Prop) :=
  ay_gegg_Conj equivalenceCoverage (tseitinWitness -> tseitinAccepted)

def ay_gegg_ModelReconstructionWitness
    (extractedCnf : Prop) (originalCnf : Prop)
    (extractedModel : Prop) (originalModel : Prop) :=
  ay_gegg_Sat extractedCnf extractedModel ->
    ay_gegg_Sat originalCnf originalModel

def ay_gegg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (extractedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_gegg_Replay extractedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_gegg_ReconstructionWitnesses
    (extractedCnf : Prop) (originalCnf : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_gegg_Conj
    (ay_gegg_ModelReconstructionWitness
      extractedCnf originalCnf extractedModel originalModel)
    (ay_gegg_UnsatProofReconstructionWitness
      originalCnf extractedCnf certificate conflict)

def ay_gegg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_gegg_Conj baselineSolver baselineAvailable

def ay_gegg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_gegg_Conj binaryFingerprint buildReproducible

def ay_gegg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_gegg_Conj validatorAccepted validatorVersion

def ay_gegg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_gegg_Conj auditAppended auditAppendOnly

def ay_gegg_AcceptedGateExtractionGuard
    (originalCnf : Prop) (extractedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedGateLedger : Prop) (gateAccepted : Prop)
    (gateCoverage : Prop)
    (definitionLedger : Prop) (definitionAccepted : Prop)
    (definitionCoverage : Prop)
    (tseitinWitness : Prop) (tseitinAccepted : Prop)
    (equivalenceCoverage : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_gegg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_gegg_DetectedGateLedger
       detectedGateLedger gateAccepted gateCoverage ->
     ay_gegg_DefinitionIntroductionLedger
       definitionLedger definitionAccepted definitionCoverage ->
     ay_gegg_TseitinEquivalenceWitness
       tseitinWitness tseitinAccepted equivalenceCoverage ->
     ay_gegg_ReconstructionWitnesses
       extractedCnf originalCnf extractedModel originalModel certificate conflict ->
     ay_gegg_Equisat originalCnf extractedCnf ->
     ay_gegg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_gegg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_gegg_ValidatorGate validatorAccepted validatorVersion ->
     ay_gegg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_gegg_GateExtractionGuardFailure
    (digestMismatch : Prop) (gateMismatch : Prop)
    (definitionMismatch : Prop) (equivalenceMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (gateMismatch -> result) ->
    (definitionMismatch -> result) ->
    (equivalenceMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_gegg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_gegg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_gegg_Conj currentCnf recompute

def ay_gegg_DiagnosticGateExtractionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (gateMismatch : Prop)
    (definitionMismatch : Prop) (equivalenceMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_gegg_Conj
    (ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch)
    (ay_gegg_Conj
      (ay_gegg_RecomputeObligation currentCnf recompute)
      (ay_gegg_NoSemanticClaim diagnostic))

def ay_gegg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_gegg_Conj exitCode claim

def ay_gegg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_gegg_Disj
    (ay_gegg_ExitCodeSound exitCode (ay_gegg_Sat originalCnf model))
    (ay_gegg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_gegg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_gegg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_gegg_conj_left
    (left : Prop) (right : Prop) :
    ay_gegg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_gegg_conj_right
    (left : Prop) (right : Prop) :
    ay_gegg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_gegg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_gegg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_gegg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_gegg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_gegg_equisat_forward
    (original : Prop) (extracted : Prop) :
    ay_gegg_Equisat original extracted -> original -> extracted := by
  intro eqsat
  exact ay_gegg_conj_left (original -> extracted) (extracted -> original) eqsat

theorem ay_gegg_equisat_backward
    (original : Prop) (extracted : Prop) :
    ay_gegg_Equisat original extracted -> extracted -> original := by
  intro eqsat
  exact ay_gegg_conj_right (original -> extracted) (extracted -> original) eqsat

theorem ay_gegg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_gegg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_gegg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_gegg_detected_gate_ledger_applies
    (detectedGateLedger : Prop) (gateAccepted : Prop)
    (gateCoverage : Prop) :
    ay_gegg_DetectedGateLedger
      detectedGateLedger gateAccepted gateCoverage ->
    detectedGateLedger -> gateAccepted := by
  intro ledger
  exact ay_gegg_conj_right
    gateCoverage (detectedGateLedger -> gateAccepted) ledger

theorem ay_gegg_definition_introduction_ledger_applies
    (definitionLedger : Prop) (definitionAccepted : Prop)
    (definitionCoverage : Prop) :
    ay_gegg_DefinitionIntroductionLedger
      definitionLedger definitionAccepted definitionCoverage ->
    definitionLedger -> definitionAccepted := by
  intro ledger
  exact ay_gegg_conj_right
    definitionCoverage (definitionLedger -> definitionAccepted) ledger

theorem ay_gegg_tseitin_equivalence_witness_applies
    (tseitinWitness : Prop) (tseitinAccepted : Prop)
    (equivalenceCoverage : Prop) :
    ay_gegg_TseitinEquivalenceWitness
      tseitinWitness tseitinAccepted equivalenceCoverage ->
    tseitinWitness -> tseitinAccepted := by
  intro witness
  exact ay_gegg_conj_right
    equivalenceCoverage (tseitinWitness -> tseitinAccepted) witness

theorem ay_gegg_model_reconstruction
    (extractedCnf : Prop) (originalCnf : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_gegg_ReconstructionWitnesses
      extractedCnf originalCnf extractedModel originalModel certificate conflict ->
    ay_gegg_Sat extractedCnf extractedModel ->
    ay_gegg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_gegg_conj_left
    (ay_gegg_ModelReconstructionWitness
      extractedCnf originalCnf extractedModel originalModel)
    (ay_gegg_UnsatProofReconstructionWitness
      originalCnf extractedCnf certificate conflict)
    witnesses

theorem ay_gegg_unsat_proof_reconstruction
    (extractedCnf : Prop) (originalCnf : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_gegg_ReconstructionWitnesses
      extractedCnf originalCnf extractedModel originalModel certificate conflict ->
    ay_gegg_Replay extractedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_gegg_conj_right
    (ay_gegg_ModelReconstructionWitness
      extractedCnf originalCnf extractedModel originalModel)
    (ay_gegg_UnsatProofReconstructionWitness
      originalCnf extractedCnf certificate conflict)
    witnesses

theorem ay_gegg_accepted_equisat
    (originalCnf : Prop) (extractedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedGateLedger : Prop) (gateAccepted : Prop)
    (gateCoverage : Prop)
    (definitionLedger : Prop) (definitionAccepted : Prop)
    (definitionCoverage : Prop)
    (tseitinWitness : Prop) (tseitinAccepted : Prop)
    (equivalenceCoverage : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_gegg_AcceptedGateExtractionGuard
      originalCnf extractedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      detectedGateLedger gateAccepted gateCoverage
      definitionLedger definitionAccepted definitionCoverage
      tseitinWitness tseitinAccepted equivalenceCoverage
      extractedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_gegg_Equisat originalCnf extractedCnf := by
  intro accepted
  exact accepted (ay_gegg_Equisat originalCnf extractedCnf)
    (fun _digestOk _gateOk _definitionOk _equivalenceOk _reconstruct
      eqsat _fallback _build _validator _audit => eqsat)

theorem ay_gegg_accepted_reconstruction
    (originalCnf : Prop) (extractedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (detectedGateLedger : Prop) (gateAccepted : Prop)
    (gateCoverage : Prop)
    (definitionLedger : Prop) (definitionAccepted : Prop)
    (definitionCoverage : Prop)
    (tseitinWitness : Prop) (tseitinAccepted : Prop)
    (equivalenceCoverage : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_gegg_AcceptedGateExtractionGuard
      originalCnf extractedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      detectedGateLedger gateAccepted gateCoverage
      definitionLedger definitionAccepted definitionCoverage
      tseitinWitness tseitinAccepted equivalenceCoverage
      extractedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_gegg_ReconstructionWitnesses
      extractedCnf originalCnf extractedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_gegg_ReconstructionWitnesses
      extractedCnf originalCnf extractedModel originalModel certificate conflict)
    (fun _digestOk _gateOk _definitionOk _equivalenceOk reconstruct _eqsat
      _fallback _build _validator _audit => reconstruct)

theorem ay_gegg_sat_pullback
    (originalCnf : Prop) (extractedCnf : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_gegg_ReconstructionWitnesses
      extractedCnf originalCnf extractedModel originalModel certificate conflict ->
    ay_gegg_Sat extractedCnf extractedModel ->
    ay_gegg_Sat originalCnf originalModel := by
  intro witnesses satExtracted
  exact ay_gegg_model_reconstruction
    extractedCnf originalCnf extractedModel originalModel
    certificate conflict witnesses satExtracted

theorem ay_gegg_unsat_pushback
    (originalCnf : Prop) (extractedCnf : Prop)
    (extractedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_gegg_ReconstructionWitnesses
      extractedCnf originalCnf extractedModel originalModel certificate conflict ->
    ay_gegg_Replay extractedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_gegg_unsat_proof_reconstruction
    extractedCnf originalCnf extractedModel originalModel
    certificate conflict witnesses replay

theorem ay_gegg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_gegg_ExitCodeSound exitCode (ay_gegg_Sat originalCnf originalModel) ->
    ay_gegg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_gegg_disj_left
    (ay_gegg_ExitCodeSound exitCode (ay_gegg_Sat originalCnf originalModel))
    (ay_gegg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_gegg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_gegg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_gegg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_gegg_disj_right
    (ay_gegg_ExitCodeSound exitCode (ay_gegg_Sat originalCnf originalModel))
    (ay_gegg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_gegg_failure_digest
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    digestMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result digest_case _gate_case _definition_case _equivalence_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_gegg_failure_gate
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    gateMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case gate_case _definition_case _equivalence_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact gate_case h

theorem ay_gegg_failure_definition
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    definitionMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case definition_case _equivalence_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact definition_case h

theorem ay_gegg_failure_equivalence
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    equivalenceMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case _definition_case equivalence_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact equivalence_case h

theorem ay_gegg_failure_reconstruction
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case _definition_case _equivalence_case
    reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_gegg_failure_baseline
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    baselineMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case _definition_case _equivalence_case
    _reconstruction_case baseline_case _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_gegg_failure_build
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case _definition_case _equivalence_case
    _reconstruction_case _baseline_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_gegg_failure_validator
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case _definition_case _equivalence_case
    _reconstruction_case _baseline_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_gegg_failure_audit
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_gegg_GateExtractionGuardFailure
      digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _gate_case _definition_case _equivalence_case
    _reconstruction_case _baseline_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_gegg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_gegg_DiagnosticGateExtractionGuard
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_gegg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_gegg_conj_right
    (ay_gegg_RecomputeObligation currentCnf recompute)
    (ay_gegg_NoSemanticClaim diagnostic)
    (ay_gegg_conj_right
      (ay_gegg_GateExtractionGuardFailure
        digestMismatch gateMismatch definitionMismatch equivalenceMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_gegg_Conj
        (ay_gegg_RecomputeObligation currentCnf recompute)
        (ay_gegg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_gegg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_gegg_DiagnosticGateExtractionGuard
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_gegg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_gegg_conj_left
    (ay_gegg_RecomputeObligation currentCnf recompute)
    (ay_gegg_NoSemanticClaim diagnostic)
    (ay_gegg_conj_right
      (ay_gegg_GateExtractionGuardFailure
        digestMismatch gateMismatch definitionMismatch equivalenceMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_gegg_Conj
        (ay_gegg_RecomputeObligation currentCnf recompute)
        (ay_gegg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_gegg_failed_gate_extraction_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_gegg_DiagnosticGateExtractionGuard
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_gegg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_gegg_Conj
      (ay_gegg_NoSemanticClaim diagnostic)
      (ay_gegg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_gegg_conj_intro
    (ay_gegg_NoSemanticClaim diagnostic)
    (ay_gegg_RecomputeObligation currentCnf recompute)
    (ay_gegg_diagnostic_no_claim
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)
    (ay_gegg_diagnostic_recompute
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_gegg_failed_gate_extraction_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_gegg_DiagnosticGateExtractionGuard
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_gegg_ExitCodeSound exitCode (ay_gegg_Sat originalCnf model) ->
    ay_gegg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_gegg_diagnostic_no_claim
    currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard

theorem ay_gegg_failed_gate_extraction_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch gateMismatch definitionMismatch equivalenceMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_gegg_DiagnosticGateExtractionGuard
      currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_gegg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_gegg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_gegg_diagnostic_no_claim
    currentCnf digestMismatch gateMismatch definitionMismatch equivalenceMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard
