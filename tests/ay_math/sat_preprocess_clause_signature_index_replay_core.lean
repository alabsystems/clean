-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-signature index replay soundness for preprocessing. The propositions
-- stand for signature logs, duplicate/subsumption candidate lookup, clause
-- coverage, representative maps, reconstruction hooks, checker replay,
-- fingerprints, fallback/build/validator/audit evidence, diagnostics, and
-- public SAT/UNSAT publication.

def ay_pcsi_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pcsi_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pcsi_Equisat (before : Prop) (after : Prop) :=
  ay_pcsi_Conj (before -> after) (after -> before)

def ay_pcsi_Sat (cnf : Prop) (model : Prop) :=
  ay_pcsi_Conj cnf model

def ay_pcsi_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pcsi_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pcsi_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pcsi_SignatureLog
    (signatureIndex : Prop) (candidateLookup : Prop)
    (signatureLog : Prop) :=
  ay_pcsi_Conj signatureLog (signatureIndex -> candidateLookup)

def ay_pcsi_ClauseCoverage
    (candidateClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pcsi_Conj coverageWitness (candidateClause -> coveredClause)

def ay_pcsi_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_pcsi_Conj representativeWitness
    (ay_pcsi_IdMatch oldRepresentative newRepresentative)

def ay_pcsi_ModelReconstruction
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop) :=
  ay_pcsi_Sat indexedCnf indexedModel ->
    ay_pcsi_Sat originalCnf originalModel

def ay_pcsi_ProofReconstruction
    (originalCnf : Prop) (indexedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcsi_Replay indexedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pcsi_CheckerReplay
    (signatureCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pcsi_Conj signatureCertificate checkerAccepted

def ay_pcsi_FingerprintAgreement
    (originalFingerprint : Prop) (indexedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcsi_Conj fingerprintWitness
    (ay_pcsi_IdMatch originalFingerprint indexedFingerprint)

def ay_pcsi_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pcsi_Conj baselineSolver baselineAvailable

def ay_pcsi_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pcsi_Conj binaryFingerprint buildReproducible

def ay_pcsi_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pcsi_Conj validatorAccepted validatorVersion

def ay_pcsi_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pcsi_Conj auditAppended auditAppendOnly

def ay_pcsi_AcceptedSignatureIndexReplay
    (originalCnf : Prop) (indexedCnf : Prop)
    (signatureIndex : Prop) (candidateLookup : Prop)
    (signatureLog : Prop)
    (candidateClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (signatureCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (indexedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pcsi_SignatureLog signatureIndex candidateLookup signatureLog ->
     ay_pcsi_ClauseCoverage candidateClause coveredClause coverageWitness ->
     ay_pcsi_RepresentativeAgreement
       oldRepresentative newRepresentative representativeWitness ->
     ay_pcsi_Equisat originalCnf indexedCnf ->
     ay_pcsi_ModelReconstruction
       indexedCnf originalCnf indexedModel originalModel ->
     ay_pcsi_ProofReconstruction
       originalCnf indexedCnf certificate conflict ->
     ay_pcsi_CheckerReplay signatureCertificate checkerAccepted ->
     ay_pcsi_FingerprintAgreement
       originalFingerprint indexedFingerprint fingerprintWitness ->
     ay_pcsi_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pcsi_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pcsi_ValidatorGate validatorAccepted validatorVersion ->
     ay_pcsi_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pcsi_SignatureIndexFailure
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop) :=
  ay_pcsi_Disj signatureCollision
    (ay_pcsi_Disj staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)))

def ay_pcsi_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pcsi_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pcsi_Conj currentCnf recompute

def ay_pcsi_DiagnosticSignatureIndexReplay
    (currentCnf : Prop)
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pcsi_Conj
    (ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay)
    (ay_pcsi_Conj
      (ay_pcsi_RecomputeObligation currentCnf recompute)
      (ay_pcsi_NoSemanticClaim diagnostic))

def ay_pcsi_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pcsi_Conj exitCode claim

def ay_pcsi_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pcsi_Disj
    (ay_pcsi_ExitCodeSound exitCode (ay_pcsi_Sat originalCnf model))
    (ay_pcsi_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pcsi_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pcsi_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcsi_conj_left
    (left : Prop) (right : Prop) :
    ay_pcsi_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcsi_conj_right
    (left : Prop) (right : Prop) :
    ay_pcsi_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcsi_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pcsi_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcsi_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pcsi_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcsi_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pcsi_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcsi_conj_left (before -> after) (after -> before) eq

theorem ay_pcsi_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pcsi_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pcsi_conj_right (before -> after) (after -> before) eq

theorem ay_pcsi_signature_candidate_lookup
    (signatureIndex : Prop) (candidateLookup : Prop)
    (signatureLog : Prop) :
    ay_pcsi_SignatureLog signatureIndex candidateLookup signatureLog ->
    signatureIndex ->
    candidateLookup := by
  intro accepted index
  exact
    (ay_pcsi_conj_right signatureLog
      (signatureIndex -> candidateLookup) accepted) index

theorem ay_pcsi_clause_coverage
    (candidateClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pcsi_ClauseCoverage
      candidateClause coveredClause coverageWitness ->
    candidateClause ->
    coveredClause := by
  intro accepted candidate
  exact
    (ay_pcsi_conj_right coverageWitness
      (candidateClause -> coveredClause) accepted) candidate

theorem ay_pcsi_representative_forward
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :
    ay_pcsi_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness ->
    oldRepresentative ->
    newRepresentative := by
  intro accepted old
  exact accepted newRepresentative
    (fun _witness ids =>
      ids newRepresentative
        (fun forward _backward => forward old))

theorem ay_pcsi_accepted_equisat
    (originalCnf : Prop) (indexedCnf : Prop)
    (signatureIndex : Prop) (candidateLookup : Prop)
    (signatureLog : Prop)
    (candidateClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (signatureCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (indexedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcsi_AcceptedSignatureIndexReplay
      originalCnf indexedCnf signatureIndex candidateLookup signatureLog
      candidateClause coveredClause coverageWitness oldRepresentative
      newRepresentative representativeWitness indexedModel originalModel
      certificate conflict signatureCertificate checkerAccepted
      originalFingerprint indexedFingerprint fingerprintWitness baselineSolver
      baselineAvailable binaryFingerprint buildReproducible validatorAccepted
      validatorVersion auditAppended auditAppendOnly ->
    ay_pcsi_Equisat originalCnf indexedCnf := by
  intro accepted
  exact accepted (ay_pcsi_Equisat originalCnf indexedCnf)
    (fun _log _coverage _representative eq _model _proof _checker
      _fingerprint _fallback _build _validator _audit => eq)

theorem ay_pcsi_accepted_checker_replay
    (originalCnf : Prop) (indexedCnf : Prop)
    (signatureIndex : Prop) (candidateLookup : Prop)
    (signatureLog : Prop)
    (candidateClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (indexedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (signatureCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (indexedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pcsi_AcceptedSignatureIndexReplay
      originalCnf indexedCnf signatureIndex candidateLookup signatureLog
      candidateClause coveredClause coverageWitness oldRepresentative
      newRepresentative representativeWitness indexedModel originalModel
      certificate conflict signatureCertificate checkerAccepted
      originalFingerprint indexedFingerprint fingerprintWitness baselineSolver
      baselineAvailable binaryFingerprint buildReproducible validatorAccepted
      validatorVersion auditAppended auditAppendOnly ->
    ay_pcsi_CheckerReplay signatureCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_pcsi_CheckerReplay signatureCertificate checkerAccepted)
    (fun _log _coverage _representative _eq _model _proof checker
      _fingerprint _fallback _build _validator _audit => checker)

theorem ay_pcsi_sat_pullback
    (indexedCnf : Prop) (originalCnf : Prop)
    (indexedModel : Prop) (originalModel : Prop) :
    ay_pcsi_ModelReconstruction
      indexedCnf originalCnf indexedModel originalModel ->
    ay_pcsi_Sat indexedCnf indexedModel ->
    ay_pcsi_Sat originalCnf originalModel := by
  intro reconstruct indexedSat
  exact reconstruct indexedSat

theorem ay_pcsi_unsat_pushback
    (originalCnf : Prop) (indexedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pcsi_ProofReconstruction
      originalCnf indexedCnf certificate conflict ->
    ay_pcsi_Replay indexedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pcsi_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pcsi_Sat originalCnf model ->
    ay_pcsi_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pcsi_disj_left
    (ay_pcsi_ExitCodeSound exitCode (ay_pcsi_Sat originalCnf model))
    (ay_pcsi_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pcsi_conj_intro exitCode
      (ay_pcsi_Sat originalCnf model) exit sat)

theorem ay_pcsi_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pcsi_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pcsi_disj_right
    (ay_pcsi_ExitCodeSound exitCode (ay_pcsi_Sat originalCnf model))
    (ay_pcsi_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pcsi_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pcsi_failure_signature_collision
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop) :
    signatureCollision ->
    ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay := by
  intro collision
  exact ay_pcsi_disj_left signatureCollision
    (ay_pcsi_Disj staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)))
    collision

theorem ay_pcsi_failure_stale_index
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop) :
    staleIndex ->
    ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay := by
  intro stale
  exact ay_pcsi_disj_right signatureCollision
    (ay_pcsi_Disj staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)))
    (ay_pcsi_disj_left staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay))
      stale)

theorem ay_pcsi_failure_representative_mismatch
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop) :
    representativeMismatch ->
    ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay := by
  intro mismatch
  exact ay_pcsi_disj_right signatureCollision
    (ay_pcsi_Disj staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)))
    (ay_pcsi_disj_right staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay))
      (ay_pcsi_disj_left representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay) mismatch))

theorem ay_pcsi_failure_missing_coverage
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop) :
    missingCoverage ->
    ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay := by
  intro missing
  exact ay_pcsi_disj_right signatureCollision
    (ay_pcsi_Disj staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)))
    (ay_pcsi_disj_right staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay))
      (ay_pcsi_disj_right representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)
        (ay_pcsi_disj_left missingCoverage uncheckedReplay missing)))

theorem ay_pcsi_failure_unchecked_replay
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop) :
    uncheckedReplay ->
    ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay := by
  intro unchecked
  exact ay_pcsi_disj_right signatureCollision
    (ay_pcsi_Disj staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)))
    (ay_pcsi_disj_right staleIndex
      (ay_pcsi_Disj representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay))
      (ay_pcsi_disj_right representativeMismatch
        (ay_pcsi_Disj missingCoverage uncheckedReplay)
        (ay_pcsi_disj_right missingCoverage uncheckedReplay unchecked)))

theorem ay_pcsi_diagnostic_no_claim
    (currentCnf : Prop)
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcsi_DiagnosticSignatureIndexReplay
      currentCnf signatureCollision staleIndex representativeMismatch
      missingCoverage uncheckedReplay recompute diagnostic ->
    ay_pcsi_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pcsi_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pcsi_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pcsi_diagnostic_recompute
    (currentCnf : Prop)
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcsi_DiagnosticSignatureIndexReplay
      currentCnf signatureCollision staleIndex representativeMismatch
      missingCoverage uncheckedReplay recompute diagnostic ->
    ay_pcsi_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pcsi_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pcsi_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pcsi_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (signatureCollision : Prop) (staleIndex : Prop)
    (representativeMismatch : Prop) (missingCoverage : Prop)
    (uncheckedReplay : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pcsi_RecomputeObligation currentCnf recompute ->
    ay_pcsi_NoSemanticClaim diagnostic ->
    ay_pcsi_DiagnosticSignatureIndexReplay
      currentCnf signatureCollision staleIndex representativeMismatch
      missingCoverage uncheckedReplay recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pcsi_conj_intro
    (ay_pcsi_SignatureIndexFailure
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay)
    (ay_pcsi_Conj
      (ay_pcsi_RecomputeObligation currentCnf recompute)
      (ay_pcsi_NoSemanticClaim diagnostic))
    (ay_pcsi_failure_unchecked_replay
      signatureCollision staleIndex representativeMismatch missingCoverage
      uncheckedReplay unchecked)
    (ay_pcsi_conj_intro
      (ay_pcsi_RecomputeObligation currentCnf recompute)
      (ay_pcsi_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
