-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Substitution-chain checkpoint replay soundness for preprocessing. The
-- propositions stand for substitution checkpoint manifests, inverse maps,
-- affected-clause coverage, trail/model reconstruction, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pscc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pscc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pscc_Equisat (before : Prop) (after : Prop) :=
  ay_pscc_Conj (before -> after) (after -> before)

def ay_pscc_Sat (cnf : Prop) (model : Prop) :=
  ay_pscc_Conj cnf model

def ay_pscc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pscc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pscc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pscc_SubstitutionCheckpointManifest
    (substitutionChain : Prop) (checkpointManifest : Prop)
    (manifestWitness : Prop) :=
  ay_pscc_Conj manifestWitness
    (substitutionChain -> checkpointManifest)

def ay_pscc_InverseMap
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop) :=
  ay_pscc_Conj inverseWitness
    (ay_pscc_Conj forwardMap inverseMap)

def ay_pscc_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pscc_Conj coverageWitness (affectedClause -> coveredClause)

def ay_pscc_TrailModelReconstruction
    (trailModelSnapshot : Prop) (checkpointManifest : Prop)
    (ledgerWitness : Prop) :=
  ay_pscc_Conj ledgerWitness
    (checkpointManifest -> trailModelSnapshot)

def ay_pscc_ModelReconstruction
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop) :=
  ay_pscc_Sat substitutedCnf substitutedModel ->
    ay_pscc_Sat originalCnf originalModel

def ay_pscc_ProofReconstruction
    (originalCnf : Prop) (substitutedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pscc_Replay substitutedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pscc_FingerprintAgreement
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pscc_Conj fingerprintWitness
    (ay_pscc_IdMatch originalFingerprint substitutedFingerprint)

def ay_pscc_CheckerReplay
    (substitutionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pscc_Conj substitutionCertificate checkerAccepted

def ay_pscc_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pscc_Conj baselineSolver baselineAvailable

def ay_pscc_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pscc_Conj binaryFingerprint buildReproducible

def ay_pscc_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pscc_Conj validatorAccepted validatorVersion

def ay_pscc_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pscc_Conj auditAppended auditAppendOnly

def ay_pscc_AcceptedSubstitutionChainCheckpointReplay
    (originalCnf : Prop) (substitutedCnf : Prop)
    (substitutionChain : Prop) (checkpointManifest : Prop)
    (manifestWitness : Prop)
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (trailModelSnapshot : Prop) (ledgerWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pscc_SubstitutionCheckpointManifest
       substitutionChain checkpointManifest manifestWitness ->
     ay_pscc_InverseMap
       forwardMap inverseMap inverseWitness ->
     ay_pscc_AffectedClauseCoverage
       affectedClause coveredClause coverageWitness ->
     ay_pscc_TrailModelReconstruction
       trailModelSnapshot checkpointManifest ledgerWitness ->
     ay_pscc_Equisat originalCnf substitutedCnf ->
     ay_pscc_ModelReconstruction
       substitutedCnf originalCnf substitutedModel originalModel ->
     ay_pscc_ProofReconstruction
       originalCnf substitutedCnf certificate conflict ->
     ay_pscc_FingerprintAgreement
       originalFingerprint substitutedFingerprint fingerprintWitness ->
     ay_pscc_CheckerReplay
       substitutionCertificate checkerAccepted ->
     ay_pscc_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pscc_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pscc_ValidatorGate validatorAccepted validatorVersion ->
     ay_pscc_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pscc_SubstitutionChainFailure
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (reconstructionGap : Prop) :=
  ay_pscc_Disj checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))

def ay_pscc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pscc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pscc_Conj currentCnf recompute

def ay_pscc_DiagnosticSubstitutionChainCheckpointReplay
    (currentCnf : Prop)
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pscc_Conj
    (ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap)
    (ay_pscc_Conj
      (ay_pscc_RecomputeObligation currentCnf recompute)
      (ay_pscc_NoSemanticClaim diagnostic))

def ay_pscc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pscc_Conj exitCode claim

def ay_pscc_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pscc_Disj
    (ay_pscc_ExitCodeSound exitCode (ay_pscc_Sat originalCnf model))
    (ay_pscc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pscc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pscc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pscc_conj_left
    (left : Prop) (right : Prop) :
    ay_pscc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pscc_conj_right
    (left : Prop) (right : Prop) :
    ay_pscc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pscc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pscc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pscc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pscc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pscc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pscc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pscc_conj_left (before -> after) (after -> before) eq

theorem ay_pscc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pscc_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pscc_conj_right (before -> after) (after -> before) eq

theorem ay_pscc_substitution_checkpoint_manifest_applies
    (substitutionChain : Prop) (checkpointManifest : Prop)
    (manifestWitness : Prop) :
    ay_pscc_SubstitutionCheckpointManifest
      substitutionChain checkpointManifest manifestWitness ->
    substitutionChain ->
    checkpointManifest := by
  intro accepted raw
  exact
    (ay_pscc_conj_right manifestWitness
      (substitutionChain -> checkpointManifest) accepted) raw

theorem ay_pscc_inverse_map_forward
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop) :
    ay_pscc_InverseMap
      forwardMap inverseMap inverseWitness ->
    forwardMap := by
  intro accepted
  exact accepted forwardMap
    (fun _ledger pair =>
      pair forwardMap
        (fun duplicate _tautology => duplicate))

theorem ay_pscc_inverse_map_backward
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop) :
    ay_pscc_InverseMap
      forwardMap inverseMap inverseWitness ->
    inverseMap := by
  intro accepted
  exact accepted inverseMap
    (fun _ledger pair =>
      pair inverseMap
        (fun _duplicate tautology => tautology))

theorem ay_pscc_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pscc_AffectedClauseCoverage
      affectedClause coveredClause coverageWitness ->
    affectedClause ->
    coveredClause := by
  intro accepted original
  exact
    (ay_pscc_conj_right coverageWitness
      (affectedClause -> coveredClause) accepted) original

theorem ay_pscc_trail_model_reconstruction_records
    (trailModelSnapshot : Prop) (checkpointManifest : Prop)
    (ledgerWitness : Prop) :
    ay_pscc_TrailModelReconstruction
      trailModelSnapshot checkpointManifest ledgerWitness ->
    checkpointManifest ->
    trailModelSnapshot := by
  intro accepted canonical
  exact
    (ay_pscc_conj_right ledgerWitness
      (checkpointManifest -> trailModelSnapshot) accepted) canonical

theorem ay_pscc_accepted_equisat
    (originalCnf : Prop) (substitutedCnf : Prop)
    (substitutionChain : Prop) (checkpointManifest : Prop)
    (manifestWitness : Prop)
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (trailModelSnapshot : Prop) (ledgerWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pscc_AcceptedSubstitutionChainCheckpointReplay
      originalCnf substitutedCnf substitutionChain checkpointManifest
      manifestWitness forwardMap inverseMap
      inverseWitness affectedClause coveredClause coverageWitness
      trailModelSnapshot ledgerWitness substitutedModel originalModel
      certificate conflict originalFingerprint substitutedFingerprint
      fingerprintWitness substitutionCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pscc_Equisat originalCnf substitutedCnf := by
  intro accepted
  exact accepted (ay_pscc_Equisat originalCnf substitutedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pscc_accepted_checker_replay
    (originalCnf : Prop) (substitutedCnf : Prop)
    (substitutionChain : Prop) (checkpointManifest : Prop)
    (manifestWitness : Prop)
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (trailModelSnapshot : Prop) (ledgerWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pscc_AcceptedSubstitutionChainCheckpointReplay
      originalCnf substitutedCnf substitutionChain checkpointManifest
      manifestWitness forwardMap inverseMap
      inverseWitness affectedClause coveredClause coverageWitness
      trailModelSnapshot ledgerWitness substitutedModel originalModel
      certificate conflict originalFingerprint substitutedFingerprint
      fingerprintWitness substitutionCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pscc_CheckerReplay substitutionCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pscc_CheckerReplay substitutionCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pscc_accepted_audit_evidence
    (originalCnf : Prop) (substitutedCnf : Prop)
    (substitutionChain : Prop) (checkpointManifest : Prop)
    (manifestWitness : Prop)
    (forwardMap : Prop) (inverseMap : Prop)
    (inverseWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (trailModelSnapshot : Prop) (ledgerWitness : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (substitutedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (substitutionCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pscc_AcceptedSubstitutionChainCheckpointReplay
      originalCnf substitutedCnf substitutionChain checkpointManifest
      manifestWitness forwardMap inverseMap
      inverseWitness affectedClause coveredClause coverageWitness
      trailModelSnapshot ledgerWitness substitutedModel originalModel
      certificate conflict originalFingerprint substitutedFingerprint
      fingerprintWitness substitutionCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pscc_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pscc_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pscc_sat_pullback
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop) :
    ay_pscc_ModelReconstruction
      substitutedCnf originalCnf substitutedModel originalModel ->
    ay_pscc_Sat substitutedCnf substitutedModel ->
    ay_pscc_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pscc_unsat_pushback
    (originalCnf : Prop) (substitutedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pscc_ProofReconstruction
      originalCnf substitutedCnf certificate conflict ->
    ay_pscc_Replay substitutedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pscc_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pscc_Sat originalCnf model ->
    ay_pscc_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pscc_disj_left
    (ay_pscc_ExitCodeSound exitCode (ay_pscc_Sat originalCnf model))
    (ay_pscc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pscc_conj_intro exitCode
      (ay_pscc_Sat originalCnf model) exit sat)

theorem ay_pscc_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pscc_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pscc_disj_right
    (ay_pscc_ExitCodeSound exitCode (ay_pscc_Sat originalCnf model))
    (ay_pscc_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pscc_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pscc_failure_checkpoint_drift
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    checkpointDrift ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro drift
  exact ay_pscc_disj_left checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    drift

theorem ay_pscc_failure_inverse_map_mismatch
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    inverseMapMismatch ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro mismatch
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_left inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      mismatch)

theorem ay_pscc_failure_coverage_gap
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    coverageGap ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro gap
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_right inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      (ay_pscc_disj_left coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))
        gap))

theorem ay_pscc_failure_stale_fingerprint
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    staleFingerprint ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro stale
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_right inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      (ay_pscc_disj_right coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))
        (ay_pscc_disj_left staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))
          stale)))

theorem ay_pscc_failure_unchecked_replay
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    uncheckedReplay ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro unchecked
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_right inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      (ay_pscc_disj_right coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))
        (ay_pscc_disj_right staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))
          (ay_pscc_disj_left uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))
            unchecked))))

theorem ay_pscc_failure_build_drift
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    buildDrift ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro drift
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_right inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      (ay_pscc_disj_right coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))
        (ay_pscc_disj_right staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))
          (ay_pscc_disj_right uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))
            (ay_pscc_disj_left buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)
              drift)))))

theorem ay_pscc_failure_audit_contradiction
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    auditContradiction ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro auditBad
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_right inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      (ay_pscc_disj_right coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))
        (ay_pscc_disj_right staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))
          (ay_pscc_disj_right uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))
            (ay_pscc_disj_right buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)
              (ay_pscc_disj_left auditContradiction reconstructionGap
                auditBad))))))

theorem ay_pscc_failure_reconstruction_gap
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop) :
    reconstructionGap ->
    ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap := by
  intro mismatch
  exact ay_pscc_disj_right checkpointDrift
    (ay_pscc_Disj inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))))
    (ay_pscc_disj_right inverseMapMismatch
      (ay_pscc_Disj coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))))
      (ay_pscc_disj_right coverageGap
        (ay_pscc_Disj staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))))
        (ay_pscc_disj_right staleFingerprint
          (ay_pscc_Disj uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)))
          (ay_pscc_disj_right uncheckedReplay
            (ay_pscc_Disj buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap))
            (ay_pscc_disj_right buildDrift
              (ay_pscc_Disj auditContradiction reconstructionGap)
              (ay_pscc_disj_right auditContradiction reconstructionGap
                mismatch))))))

theorem ay_pscc_diagnostic_no_claim
    (currentCnf : Prop)
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pscc_DiagnosticSubstitutionChainCheckpointReplay
      currentCnf checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap recompute diagnostic ->
    ay_pscc_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pscc_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pscc_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pscc_diagnostic_recompute
    (currentCnf : Prop)
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pscc_DiagnosticSubstitutionChainCheckpointReplay
      currentCnf checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap recompute diagnostic ->
    ay_pscc_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pscc_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pscc_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pscc_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (checkpointDrift : Prop) (inverseMapMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (reconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pscc_RecomputeObligation currentCnf recompute ->
    ay_pscc_NoSemanticClaim diagnostic ->
    ay_pscc_DiagnosticSubstitutionChainCheckpointReplay
      currentCnf checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pscc_conj_intro
    (ay_pscc_SubstitutionChainFailure
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap)
    (ay_pscc_Conj
      (ay_pscc_RecomputeObligation currentCnf recompute)
      (ay_pscc_NoSemanticClaim diagnostic))
    (ay_pscc_failure_unchecked_replay
      checkpointDrift inverseMapMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction reconstructionGap unchecked)
    (ay_pscc_conj_intro
      (ay_pscc_RecomputeObligation currentCnf recompute)
      (ay_pscc_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
