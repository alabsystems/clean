-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Unit-subsumption preprocessing guard soundness.
-- The propositions stand for formula digests, unit literal ledgers,
-- subsumed-clause ledgers, shortened-clause witnesses, model/proof
-- reconstruction, fallback/build/validator gates, audit transcripts,
-- diagnostics, and public SAT/UNSAT reports.

def ay_usgg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_usgg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_usgg_Equisat (original : Prop) (reduced : Prop) :=
  ay_usgg_Conj (original -> reduced) (reduced -> original)

def ay_usgg_Sat (cnf : Prop) (model : Prop) :=
  ay_usgg_Conj cnf model

def ay_usgg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_usgg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_usgg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_usgg_UnitLiteralLedger
    (unitLiteralLedger : Prop) (unitAccepted : Prop)
    (unitCoverage : Prop) :=
  ay_usgg_Conj unitCoverage (unitLiteralLedger -> unitAccepted)

def ay_usgg_SubsumedClauseLedger
    (subsumedClauseLedger : Prop) (subsumedAccepted : Prop)
    (subsumedCoverage : Prop) :=
  ay_usgg_Conj subsumedCoverage
    (subsumedClauseLedger -> subsumedAccepted)

def ay_usgg_ShortenedClauseWitness
    (shortenedClauseWitness : Prop) (shorteningAccepted : Prop)
    (shorteningCoverage : Prop) :=
  ay_usgg_Conj shorteningCoverage
    (shortenedClauseWitness -> shorteningAccepted)

def ay_usgg_ModelReconstructionWitness
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_usgg_Sat reducedCnf reducedModel ->
    ay_usgg_Sat originalCnf originalModel

def ay_usgg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_usgg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_usgg_ReconstructionWitnesses
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_usgg_Conj
    (ay_usgg_ModelReconstructionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_usgg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)

def ay_usgg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_usgg_Conj baselineSolver baselineAvailable

def ay_usgg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_usgg_Conj binaryFingerprint buildReproducible

def ay_usgg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_usgg_Conj validatorAccepted validatorVersion

def ay_usgg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_usgg_Conj auditAppended auditAppendOnly

def ay_usgg_AcceptedUnitSubsumptionGuard
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (unitLiteralLedger : Prop) (unitAccepted : Prop)
    (unitCoverage : Prop)
    (subsumedClauseLedger : Prop) (subsumedAccepted : Prop)
    (subsumedCoverage : Prop)
    (shortenedClauseWitness : Prop) (shorteningAccepted : Prop)
    (shorteningCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_usgg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_usgg_UnitLiteralLedger
       unitLiteralLedger unitAccepted unitCoverage ->
     ay_usgg_SubsumedClauseLedger
       subsumedClauseLedger subsumedAccepted subsumedCoverage ->
     ay_usgg_ShortenedClauseWitness
       shortenedClauseWitness shorteningAccepted shorteningCoverage ->
     ay_usgg_ReconstructionWitnesses
       reducedCnf originalCnf reducedModel originalModel certificate conflict ->
     ay_usgg_Equisat originalCnf reducedCnf ->
     ay_usgg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_usgg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_usgg_ValidatorGate validatorAccepted validatorVersion ->
     ay_usgg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_usgg_UnitSubsumptionGuardFailure
    (digestMismatch : Prop) (unitMismatch : Prop)
    (subsumedMismatch : Prop) (shorteningMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (unitMismatch -> result) ->
    (subsumedMismatch -> result) ->
    (shorteningMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_usgg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_usgg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_usgg_Conj currentCnf recompute

def ay_usgg_DiagnosticUnitSubsumptionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (unitMismatch : Prop)
    (subsumedMismatch : Prop) (shorteningMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_usgg_Conj
    (ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch)
    (ay_usgg_Conj
      (ay_usgg_RecomputeObligation currentCnf recompute)
      (ay_usgg_NoSemanticClaim diagnostic))

def ay_usgg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_usgg_Conj exitCode claim

def ay_usgg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_usgg_Disj
    (ay_usgg_ExitCodeSound exitCode (ay_usgg_Sat originalCnf model))
    (ay_usgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_usgg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_usgg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_usgg_conj_left
    (left : Prop) (right : Prop) :
    ay_usgg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_usgg_conj_right
    (left : Prop) (right : Prop) :
    ay_usgg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_usgg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_usgg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_usgg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_usgg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_usgg_equisat_forward
    (original : Prop) (reduced : Prop) :
    ay_usgg_Equisat original reduced -> original -> reduced := by
  intro eqsat
  exact ay_usgg_conj_left (original -> reduced) (reduced -> original) eqsat

theorem ay_usgg_equisat_backward
    (original : Prop) (reduced : Prop) :
    ay_usgg_Equisat original reduced -> reduced -> original := by
  intro eqsat
  exact ay_usgg_conj_right (original -> reduced) (reduced -> original) eqsat

theorem ay_usgg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_usgg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_usgg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_usgg_unit_literal_ledger_applies
    (unitLiteralLedger : Prop) (unitAccepted : Prop)
    (unitCoverage : Prop) :
    ay_usgg_UnitLiteralLedger
      unitLiteralLedger unitAccepted unitCoverage ->
    unitLiteralLedger -> unitAccepted := by
  intro ledger
  exact ay_usgg_conj_right
    unitCoverage (unitLiteralLedger -> unitAccepted) ledger

theorem ay_usgg_subsumed_clause_ledger_applies
    (subsumedClauseLedger : Prop) (subsumedAccepted : Prop)
    (subsumedCoverage : Prop) :
    ay_usgg_SubsumedClauseLedger
      subsumedClauseLedger subsumedAccepted subsumedCoverage ->
    subsumedClauseLedger -> subsumedAccepted := by
  intro ledger
  exact ay_usgg_conj_right
    subsumedCoverage (subsumedClauseLedger -> subsumedAccepted) ledger

theorem ay_usgg_shortened_clause_witness_applies
    (shortenedClauseWitness : Prop) (shorteningAccepted : Prop)
    (shorteningCoverage : Prop) :
    ay_usgg_ShortenedClauseWitness
      shortenedClauseWitness shorteningAccepted shorteningCoverage ->
    shortenedClauseWitness -> shorteningAccepted := by
  intro witness
  exact ay_usgg_conj_right
    shorteningCoverage (shortenedClauseWitness -> shorteningAccepted) witness

theorem ay_usgg_model_reconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_usgg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_usgg_Sat reducedCnf reducedModel ->
    ay_usgg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_usgg_conj_left
    (ay_usgg_ModelReconstructionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_usgg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_usgg_unsat_proof_reconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_usgg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_usgg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_usgg_conj_right
    (ay_usgg_ModelReconstructionWitness
      reducedCnf originalCnf reducedModel originalModel)
    (ay_usgg_UnsatProofReconstructionWitness
      originalCnf reducedCnf certificate conflict)
    witnesses

theorem ay_usgg_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (unitLiteralLedger : Prop) (unitAccepted : Prop)
    (unitCoverage : Prop)
    (subsumedClauseLedger : Prop) (subsumedAccepted : Prop)
    (subsumedCoverage : Prop)
    (shortenedClauseWitness : Prop) (shorteningAccepted : Prop)
    (shorteningCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_usgg_AcceptedUnitSubsumptionGuard
      originalCnf reducedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      unitLiteralLedger unitAccepted unitCoverage
      subsumedClauseLedger subsumedAccepted subsumedCoverage
      shortenedClauseWitness shorteningAccepted shorteningCoverage
      reducedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_usgg_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_usgg_Equisat originalCnf reducedCnf)
    (fun _digestOk _unitOk _subsumedOk _shorteningOk _reconstruct eqsat
      _fallback _build _validator _audit => eqsat)

theorem ay_usgg_accepted_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (unitLiteralLedger : Prop) (unitAccepted : Prop)
    (unitCoverage : Prop)
    (subsumedClauseLedger : Prop) (subsumedAccepted : Prop)
    (subsumedCoverage : Prop)
    (shortenedClauseWitness : Prop) (shorteningAccepted : Prop)
    (shorteningCoverage : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_usgg_AcceptedUnitSubsumptionGuard
      originalCnf reducedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      unitLiteralLedger unitAccepted unitCoverage
      subsumedClauseLedger subsumedAccepted subsumedCoverage
      shortenedClauseWitness shorteningAccepted shorteningCoverage
      reducedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_usgg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_usgg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict)
    (fun _digestOk _unitOk _subsumedOk _shorteningOk reconstruct _eqsat
      _fallback _build _validator _audit => reconstruct)

theorem ay_usgg_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_usgg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_usgg_Sat reducedCnf reducedModel ->
    ay_usgg_Sat originalCnf originalModel := by
  intro witnesses satReduced
  exact ay_usgg_model_reconstruction
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses satReduced

theorem ay_usgg_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_usgg_ReconstructionWitnesses
      reducedCnf originalCnf reducedModel originalModel certificate conflict ->
    ay_usgg_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_usgg_unsat_proof_reconstruction
    reducedCnf originalCnf reducedModel originalModel
    certificate conflict witnesses replay

theorem ay_usgg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_usgg_ExitCodeSound exitCode (ay_usgg_Sat originalCnf originalModel) ->
    ay_usgg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_usgg_disj_left
    (ay_usgg_ExitCodeSound exitCode (ay_usgg_Sat originalCnf originalModel))
    (ay_usgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_usgg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_usgg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_usgg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_usgg_disj_right
    (ay_usgg_ExitCodeSound exitCode (ay_usgg_Sat originalCnf originalModel))
    (ay_usgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_usgg_failure_digest
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    digestMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result digest_case _unit_case _subsumed_case _shortening_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_usgg_failure_unit
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    unitMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case unit_case _subsumed_case _shortening_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact unit_case h

theorem ay_usgg_failure_subsumed
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    subsumedMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case subsumed_case _shortening_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact subsumed_case h

theorem ay_usgg_failure_shortening
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    shorteningMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case _subsumed_case shortening_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact shortening_case h

theorem ay_usgg_failure_reconstruction
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case _subsumed_case _shortening_case
    reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_usgg_failure_baseline
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    baselineMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case _subsumed_case _shortening_case
    _reconstruction_case baseline_case _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_usgg_failure_build
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case _subsumed_case _shortening_case
    _reconstruction_case _baseline_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_usgg_failure_validator
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case _subsumed_case _shortening_case
    _reconstruction_case _baseline_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_usgg_failure_audit
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_usgg_UnitSubsumptionGuardFailure
      digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _unit_case _subsumed_case _shortening_case
    _reconstruction_case _baseline_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_usgg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_usgg_DiagnosticUnitSubsumptionGuard
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_usgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_usgg_conj_right
    (ay_usgg_RecomputeObligation currentCnf recompute)
    (ay_usgg_NoSemanticClaim diagnostic)
    (ay_usgg_conj_right
      (ay_usgg_UnitSubsumptionGuardFailure
        digestMismatch unitMismatch subsumedMismatch shorteningMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_usgg_Conj
        (ay_usgg_RecomputeObligation currentCnf recompute)
        (ay_usgg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_usgg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_usgg_DiagnosticUnitSubsumptionGuard
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_usgg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_usgg_conj_left
    (ay_usgg_RecomputeObligation currentCnf recompute)
    (ay_usgg_NoSemanticClaim diagnostic)
    (ay_usgg_conj_right
      (ay_usgg_UnitSubsumptionGuardFailure
        digestMismatch unitMismatch subsumedMismatch shorteningMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_usgg_Conj
        (ay_usgg_RecomputeObligation currentCnf recompute)
        (ay_usgg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_usgg_failed_unit_subsumption_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_usgg_DiagnosticUnitSubsumptionGuard
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_usgg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_usgg_Conj
      (ay_usgg_NoSemanticClaim diagnostic)
      (ay_usgg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_usgg_conj_intro
    (ay_usgg_NoSemanticClaim diagnostic)
    (ay_usgg_RecomputeObligation currentCnf recompute)
    (ay_usgg_diagnostic_no_claim
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)
    (ay_usgg_diagnostic_recompute
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_usgg_failed_unit_subsumption_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_usgg_DiagnosticUnitSubsumptionGuard
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_usgg_ExitCodeSound exitCode (ay_usgg_Sat originalCnf model) ->
    ay_usgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_usgg_diagnostic_no_claim
    currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard

theorem ay_usgg_failed_unit_subsumption_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch unitMismatch subsumedMismatch shorteningMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_usgg_DiagnosticUnitSubsumptionGuard
      currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_usgg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_usgg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_usgg_diagnostic_no_claim
    currentCnf digestMismatch unitMismatch subsumedMismatch shorteningMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard
