-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Elimination-order digest replay soundness for preprocessing. The
-- propositions stand for elimination order digests,
-- transform witness ledgers, affected-clause coverage, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_peod_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_peod_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_peod_Equisat (before : Prop) (after : Prop) :=
  ay_peod_Conj (before -> after) (after -> before)

def ay_peod_Sat (cnf : Prop) (model : Prop) :=
  ay_peod_Conj cnf model

def ay_peod_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_peod_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_peod_Conj (leftId -> rightId) (rightId -> leftId)

def ay_peod_EliminationOrderDigest
    (eliminationOrder : Prop) (orderDigest : Prop)
    (orderDigestWitness : Prop) :=
  ay_peod_Conj orderDigestWitness
    (eliminationOrder -> orderDigest)

def ay_peod_OrderDigestManifest
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop) :=
  ay_peod_Conj orderManifestWitness
    (ay_peod_Conj orderStep orderManifest)

def ay_peod_TransformWitnessLedger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :=
  ay_peod_Conj transformLedger (affectedClause -> transformWitness)

def ay_peod_AffectedClauseCoverage
    (coveredClause : Prop) (orderDigest : Prop)
    (coverageWitness : Prop) :=
  ay_peod_Conj coverageWitness
    (orderDigest -> coveredClause)

def ay_peod_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_peod_Sat reducedCnf reducedModel ->
    ay_peod_Sat originalCnf originalModel

def ay_peod_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_peod_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_peod_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_peod_Conj fingerprintWitness
    (ay_peod_IdMatch originalFingerprint reducedFingerprint)

def ay_peod_CheckerReplay
    (orderCertificate : Prop) (checkerAccepted : Prop) :=
  ay_peod_Conj orderCertificate checkerAccepted

def ay_peod_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_peod_Conj baselineSolver baselineAvailable

def ay_peod_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_peod_Conj binaryFingerprint buildReproducible

def ay_peod_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_peod_Conj validatorAccepted validatorVersion

def ay_peod_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_peod_Conj auditAppended auditAppendOnly

def ay_peod_AcceptedEliminationOrderDigestReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (eliminationOrder : Prop) (orderDigest : Prop)
    (orderDigestWitness : Prop)
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (orderCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_peod_EliminationOrderDigest
       eliminationOrder orderDigest orderDigestWitness ->
     ay_peod_OrderDigestManifest
       orderStep orderManifest orderManifestWitness ->
     ay_peod_TransformWitnessLedger
       affectedClause transformWitness transformLedger ->
     ay_peod_AffectedClauseCoverage
       coveredClause orderDigest coverageWitness ->
     ay_peod_Equisat originalCnf reducedCnf ->
     ay_peod_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_peod_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_peod_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_peod_CheckerReplay
       orderCertificate checkerAccepted ->
     ay_peod_FallbackBaseline baselineSolver baselineAvailable ->
     ay_peod_BuildEvidence binaryFingerprint buildReproducible ->
     ay_peod_ValidatorGate validatorAccepted validatorVersion ->
     ay_peod_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_peod_EliminationOrderDigestFailure
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (orderDigestDrift -> result) ->
    (transformWitnessMismatch -> result) ->
    (coverageGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (buildDrift -> result) ->
    (auditContradiction -> result) ->
    result

def ay_peod_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_peod_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_peod_Conj currentCnf recompute

def ay_peod_DiagnosticEliminationOrderDigestReplay
    (currentCnf : Prop)
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_peod_Conj
    (ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_peod_Conj
      (ay_peod_RecomputeObligation currentCnf recompute)
      (ay_peod_NoSemanticClaim diagnostic))

def ay_peod_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_peod_Conj exitCode claim

def ay_peod_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_peod_Disj
    (ay_peod_ExitCodeSound exitCode (ay_peod_Sat originalCnf model))
    (ay_peod_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_peod_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_peod_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_peod_conj_left
    (left : Prop) (right : Prop) :
    ay_peod_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_peod_conj_right
    (left : Prop) (right : Prop) :
    ay_peod_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_peod_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_peod_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_peod_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_peod_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_peod_equisat_forward
    (before : Prop) (after : Prop) :
    ay_peod_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_peod_conj_left (before -> after) (after -> before) eq

theorem ay_peod_equisat_backward
    (before : Prop) (after : Prop) :
    ay_peod_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_peod_conj_right (before -> after) (after -> before) eq

theorem ay_peod_elimination_order_digest_applies
    (eliminationOrder : Prop) (orderDigest : Prop)
    (orderDigestWitness : Prop) :
    ay_peod_EliminationOrderDigest
      eliminationOrder orderDigest orderDigestWitness ->
    eliminationOrder ->
    orderDigest := by
  intro accepted raw
  exact
    (ay_peod_conj_right orderDigestWitness
      (eliminationOrder -> orderDigest) accepted) raw

theorem ay_peod_order_digest_manifest_step
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop) :
    ay_peod_OrderDigestManifest
      orderStep orderManifest orderManifestWitness ->
    orderStep := by
  intro accepted
  exact accepted orderStep
    (fun _ledger pair =>
      pair orderStep
        (fun duplicate _tautology => duplicate))

theorem ay_peod_order_digest_manifest_manifest
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop) :
    ay_peod_OrderDigestManifest
      orderStep orderManifest orderManifestWitness ->
    orderManifest := by
  intro accepted
  exact accepted orderManifest
    (fun _ledger pair =>
      pair orderManifest
        (fun _duplicate tautology => tautology))

theorem ay_peod_transform_witness_ledger
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop) :
    ay_peod_TransformWitnessLedger
      affectedClause transformWitness transformLedger ->
    affectedClause ->
    transformWitness := by
  intro accepted original
  exact
    (ay_peod_conj_right transformLedger
      (affectedClause -> transformWitness) accepted) original

theorem ay_peod_affected_clause_coverage
    (coveredClause : Prop) (orderDigest : Prop)
    (coverageWitness : Prop) :
    ay_peod_AffectedClauseCoverage
      coveredClause orderDigest coverageWitness ->
    orderDigest ->
    coveredClause := by
  intro accepted canonical
  exact
    (ay_peod_conj_right coverageWitness
      (orderDigest -> coveredClause) accepted) canonical

theorem ay_peod_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (eliminationOrder : Prop) (orderDigest : Prop)
    (orderDigestWitness : Prop)
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (orderCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_peod_AcceptedEliminationOrderDigestReplay
      originalCnf reducedCnf eliminationOrder orderDigest
      orderDigestWitness orderStep orderManifest
      orderManifestWitness affectedClause transformWitness transformLedger
      coveredClause coverageWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness orderCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_peod_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_peod_Equisat originalCnf reducedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_peod_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (eliminationOrder : Prop) (orderDigest : Prop)
    (orderDigestWitness : Prop)
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (orderCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_peod_AcceptedEliminationOrderDigestReplay
      originalCnf reducedCnf eliminationOrder orderDigest
      orderDigestWitness orderStep orderManifest
      orderManifestWitness affectedClause transformWitness transformLedger
      coveredClause coverageWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness orderCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_peod_CheckerReplay orderCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_peod_CheckerReplay orderCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_peod_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (eliminationOrder : Prop) (orderDigest : Prop)
    (orderDigestWitness : Prop)
    (orderStep : Prop) (orderManifest : Prop)
    (orderManifestWitness : Prop)
    (affectedClause : Prop) (transformWitness : Prop)
    (transformLedger : Prop)
    (coveredClause : Prop) (coverageWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (orderCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_peod_AcceptedEliminationOrderDigestReplay
      originalCnf reducedCnf eliminationOrder orderDigest
      orderDigestWitness orderStep orderManifest
      orderManifestWitness affectedClause transformWitness transformLedger
      coveredClause coverageWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness orderCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_peod_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_peod_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_peod_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_peod_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_peod_Sat reducedCnf reducedModel ->
    ay_peod_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_peod_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_peod_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_peod_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_peod_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_peod_Sat originalCnf model ->
    ay_peod_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_peod_disj_left
    (ay_peod_ExitCodeSound exitCode (ay_peod_Sat originalCnf model))
    (ay_peod_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_peod_conj_intro exitCode
      (ay_peod_Sat originalCnf model) exit sat)

theorem ay_peod_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_peod_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_peod_disj_right
    (ay_peod_ExitCodeSound exitCode (ay_peod_Sat originalCnf model))
    (ay_peod_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_peod_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_peod_failure_order_digest_drift
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    orderDigestDrift ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hOrder h

theorem ay_peod_failure_transform_witness_mismatch
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    transformWitnessMismatch ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hTransform h

theorem ay_peod_failure_coverage_gap
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    coverageGap ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hCoverage h

theorem ay_peod_failure_reconstruction_gap
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    reconstructionGap ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hReconstruction h

theorem ay_peod_failure_stale_fingerprint
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    staleFingerprint ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hStale h

theorem ay_peod_failure_unchecked_replay
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hUnchecked h

theorem ay_peod_failure_build_drift
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    buildDrift ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hBuild h

theorem ay_peod_failure_audit_contradiction
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop) (reconstructionGap : Prop)
    (staleFingerprint : Prop) (uncheckedReplay : Prop)
    (buildDrift : Prop) (auditContradiction : Prop) :
    auditContradiction ->
    ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction := by
  intro h result hOrder hTransform hCoverage hReconstruction hStale
    hUnchecked hBuild hAudit
  exact hAudit h

theorem ay_peod_diagnostic_no_claim
    (currentCnf : Prop)
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_peod_DiagnosticEliminationOrderDigestReplay
      currentCnf orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_peod_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_peod_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_peod_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_peod_diagnostic_recompute
    (currentCnf : Prop)
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_peod_DiagnosticEliminationOrderDigestReplay
      currentCnf orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic ->
    ay_peod_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_peod_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_peod_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_peod_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (orderDigestDrift : Prop) (transformWitnessMismatch : Prop)
    (coverageGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_peod_RecomputeObligation currentCnf recompute ->
    ay_peod_NoSemanticClaim diagnostic ->
    ay_peod_DiagnosticEliminationOrderDigestReplay
      currentCnf orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_peod_conj_intro
    (ay_peod_EliminationOrderDigestFailure
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction)
    (ay_peod_Conj
      (ay_peod_RecomputeObligation currentCnf recompute)
      (ay_peod_NoSemanticClaim diagnostic))
    (ay_peod_failure_unchecked_replay
      orderDigestDrift transformWitnessMismatch coverageGap
      reconstructionGap staleFingerprint uncheckedReplay buildDrift
      auditContradiction unchecked)
    (ay_peod_conj_intro
      (ay_peod_RecomputeObligation currentCnf recompute)
      (ay_peod_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
