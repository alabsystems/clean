-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalence-class elimination replay soundness for preprocessing. The
-- propositions stand for equivalence class manifests, representative maps,
-- affected-clause coverage, inverse reconstruction, formula
-- fingerprints, checker replay, fallback baseline, build evidence, validator
-- gates, audit evidence, diagnostics, and public SAT/UNSAT reports.

def ay_pece_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pece_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pece_Equisat (before : Prop) (after : Prop) :=
  ay_pece_Conj (before -> after) (after -> before)

def ay_pece_Sat (cnf : Prop) (model : Prop) :=
  ay_pece_Conj cnf model

def ay_pece_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pece_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pece_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pece_EquivalenceClassManifest
    (equivalenceClass : Prop) (classManifest : Prop)
    (classWitness : Prop) :=
  ay_pece_Conj classWitness
    (equivalenceClass -> classManifest)

def ay_pece_RepresentativeMap
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop) :=
  ay_pece_Conj representativeWitness
    (ay_pece_Conj eliminatedLiteral representativeLiteral)

def ay_pece_AffectedClauseCoverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :=
  ay_pece_Conj coverageWitness (affectedClause -> coveredClause)

def ay_pece_InverseReconstruction
    (inverseReconstruction : Prop) (classManifest : Prop)
    (ledgerWitness : Prop) :=
  ay_pece_Conj ledgerWitness
    (classManifest -> inverseReconstruction)

def ay_pece_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_pece_Sat reducedCnf reducedModel ->
    ay_pece_Sat originalCnf originalModel

def ay_pece_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pece_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pece_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pece_Conj fingerprintWitness
    (ay_pece_IdMatch originalFingerprint reducedFingerprint)

def ay_pece_CheckerReplay
    (equivalenceCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pece_Conj equivalenceCertificate checkerAccepted

def ay_pece_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_pece_Conj baselineSolver baselineAvailable

def ay_pece_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_pece_Conj binaryFingerprint buildReproducible

def ay_pece_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_pece_Conj validatorAccepted validatorVersion

def ay_pece_AuditEvidence
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_pece_Conj auditAppended auditAppendOnly

def ay_pece_AcceptedEquivalenceClassEliminationReplay
    (originalCnf : Prop) (reducedCnf : Prop)
    (equivalenceClass : Prop) (classManifest : Prop)
    (classWitness : Prop)
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (inverseReconstruction : Prop) (ledgerWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (equivalenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_pece_EquivalenceClassManifest
       equivalenceClass classManifest classWitness ->
     ay_pece_RepresentativeMap
       eliminatedLiteral representativeLiteral representativeWitness ->
     ay_pece_AffectedClauseCoverage
       affectedClause coveredClause coverageWitness ->
     ay_pece_InverseReconstruction
       inverseReconstruction classManifest ledgerWitness ->
     ay_pece_Equisat originalCnf reducedCnf ->
     ay_pece_ModelReconstruction
       reducedCnf originalCnf reducedModel originalModel ->
     ay_pece_ProofReconstruction
       originalCnf reducedCnf certificate conflict ->
     ay_pece_FingerprintAgreement
       originalFingerprint reducedFingerprint fingerprintWitness ->
     ay_pece_CheckerReplay
       equivalenceCertificate checkerAccepted ->
     ay_pece_FallbackBaseline baselineSolver baselineAvailable ->
     ay_pece_BuildEvidence binaryFingerprint buildReproducible ->
     ay_pece_ValidatorGate validatorAccepted validatorVersion ->
     ay_pece_AuditEvidence auditAppended auditAppendOnly ->
     result) -> result

def ay_pece_EquivalenceClassFailure
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop)
    (inverseReconstructionGap : Prop) :=
  ay_pece_Disj classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))

def ay_pece_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pece_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pece_Conj currentCnf recompute

def ay_pece_DiagnosticEquivalenceClassEliminationReplay
    (currentCnf : Prop)
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pece_Conj
    (ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap)
    (ay_pece_Conj
      (ay_pece_RecomputeObligation currentCnf recompute)
      (ay_pece_NoSemanticClaim diagnostic))

def ay_pece_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pece_Conj exitCode claim

def ay_pece_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pece_Disj
    (ay_pece_ExitCodeSound exitCode (ay_pece_Sat originalCnf model))
    (ay_pece_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_pece_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pece_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pece_conj_left
    (left : Prop) (right : Prop) :
    ay_pece_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pece_conj_right
    (left : Prop) (right : Prop) :
    ay_pece_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pece_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pece_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pece_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pece_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pece_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pece_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pece_conj_left (before -> after) (after -> before) eq

theorem ay_pece_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pece_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pece_conj_right (before -> after) (after -> before) eq

theorem ay_pece_equivalence_class_manifest_applies
    (equivalenceClass : Prop) (classManifest : Prop)
    (classWitness : Prop) :
    ay_pece_EquivalenceClassManifest
      equivalenceClass classManifest classWitness ->
    equivalenceClass ->
    classManifest := by
  intro accepted raw
  exact
    (ay_pece_conj_right classWitness
      (equivalenceClass -> classManifest) accepted) raw

theorem ay_pece_representative_map_eliminated
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop) :
    ay_pece_RepresentativeMap
      eliminatedLiteral representativeLiteral representativeWitness ->
    eliminatedLiteral := by
  intro accepted
  exact accepted eliminatedLiteral
    (fun _ledger pair =>
      pair eliminatedLiteral
        (fun duplicate _tautology => duplicate))

theorem ay_pece_representative_map_representative
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop) :
    ay_pece_RepresentativeMap
      eliminatedLiteral representativeLiteral representativeWitness ->
    representativeLiteral := by
  intro accepted
  exact accepted representativeLiteral
    (fun _ledger pair =>
      pair representativeLiteral
        (fun _duplicate tautology => tautology))

theorem ay_pece_affected_clause_coverage
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop) :
    ay_pece_AffectedClauseCoverage
      affectedClause coveredClause coverageWitness ->
    affectedClause ->
    coveredClause := by
  intro accepted original
  exact
    (ay_pece_conj_right coverageWitness
      (affectedClause -> coveredClause) accepted) original

theorem ay_pece_inverse_reconstruction_records
    (inverseReconstruction : Prop) (classManifest : Prop)
    (ledgerWitness : Prop) :
    ay_pece_InverseReconstruction
      inverseReconstruction classManifest ledgerWitness ->
    classManifest ->
    inverseReconstruction := by
  intro accepted canonical
  exact
    (ay_pece_conj_right ledgerWitness
      (classManifest -> inverseReconstruction) accepted) canonical

theorem ay_pece_accepted_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (equivalenceClass : Prop) (classManifest : Prop)
    (classWitness : Prop)
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (inverseReconstruction : Prop) (ledgerWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (equivalenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pece_AcceptedEquivalenceClassEliminationReplay
      originalCnf reducedCnf equivalenceClass classManifest
      classWitness eliminatedLiteral representativeLiteral
      representativeWitness affectedClause coveredClause coverageWitness
      inverseReconstruction ledgerWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness equivalenceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pece_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted (ay_pece_Equisat originalCnf reducedCnf)
    (fun _order _accounting _coverage _ledger eq _model _proof
      _fingerprint _checker _fallback _build _validator _audit => eq)

theorem ay_pece_accepted_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (equivalenceClass : Prop) (classManifest : Prop)
    (classWitness : Prop)
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (inverseReconstruction : Prop) (ledgerWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (equivalenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pece_AcceptedEquivalenceClassEliminationReplay
      originalCnf reducedCnf equivalenceClass classManifest
      classWitness eliminatedLiteral representativeLiteral
      representativeWitness affectedClause coveredClause coverageWitness
      inverseReconstruction ledgerWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness equivalenceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pece_CheckerReplay equivalenceCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pece_CheckerReplay equivalenceCertificate checkerAccepted)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint checker _fallback _build _validator _audit => checker)

theorem ay_pece_accepted_audit_evidence
    (originalCnf : Prop) (reducedCnf : Prop)
    (equivalenceClass : Prop) (classManifest : Prop)
    (classWitness : Prop)
    (eliminatedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (affectedClause : Prop) (coveredClause : Prop)
    (coverageWitness : Prop)
    (inverseReconstruction : Prop) (ledgerWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (equivalenceCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_pece_AcceptedEquivalenceClassEliminationReplay
      originalCnf reducedCnf equivalenceClass classManifest
      classWitness eliminatedLiteral representativeLiteral
      representativeWitness affectedClause coveredClause coverageWitness
      inverseReconstruction ledgerWitness reducedModel originalModel
      certificate conflict originalFingerprint reducedFingerprint
      fingerprintWitness equivalenceCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_pece_AuditEvidence auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_pece_AuditEvidence auditAppended auditAppendOnly)
    (fun _order _accounting _coverage _ledger _eq _model _proof
      _fingerprint _checker _fallback _build _validator audit => audit)

theorem ay_pece_sat_pullback
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    ay_pece_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel ->
    ay_pece_Sat reducedCnf reducedModel ->
    ay_pece_Sat originalCnf originalModel := by
  intro reconstruct canonicalSat
  exact reconstruct canonicalSat

theorem ay_pece_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_pece_ProofReconstruction
      originalCnf reducedCnf certificate conflict ->
    ay_pece_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro reconstruct replay cert original
  exact reconstruct replay cert original

theorem ay_pece_public_sat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    ay_pece_Sat originalCnf model ->
    ay_pece_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit sat
  exact ay_pece_disj_left
    (ay_pece_ExitCodeSound exitCode (ay_pece_Sat originalCnf model))
    (ay_pece_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pece_conj_intro exitCode
      (ay_pece_Sat originalCnf model) exit sat)

theorem ay_pece_public_unsat_sound
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    exitCode ->
    (certificate -> originalCnf -> conflict) ->
    ay_pece_PublicResult
      originalCnf model certificate conflict exitCode := by
  intro exit replay
  exact ay_pece_disj_right
    (ay_pece_ExitCodeSound exitCode (ay_pece_Sat originalCnf model))
    (ay_pece_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    (ay_pece_conj_intro exitCode
      (certificate -> originalCnf -> conflict) exit replay)

theorem ay_pece_failure_class_drift
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    classDrift ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro drift
  exact ay_pece_disj_left classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    drift

theorem ay_pece_failure_representative_map_mismatch
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    representativeLiteralMismatch ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro mismatch
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_left representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      mismatch)

theorem ay_pece_failure_coverage_gap
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    coverageGap ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro gap
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_right representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      (ay_pece_disj_left coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))
        gap))

theorem ay_pece_failure_stale_fingerprint
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    staleFingerprint ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro stale
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_right representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      (ay_pece_disj_right coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))
        (ay_pece_disj_left staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))
          stale)))

theorem ay_pece_failure_unchecked_replay
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    uncheckedReplay ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro unchecked
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_right representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      (ay_pece_disj_right coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))
        (ay_pece_disj_right staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))
          (ay_pece_disj_left uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))
            unchecked))))

theorem ay_pece_failure_build_drift
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    buildDrift ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro drift
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_right representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      (ay_pece_disj_right coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))
        (ay_pece_disj_right staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))
          (ay_pece_disj_right uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))
            (ay_pece_disj_left buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)
              drift)))))

theorem ay_pece_failure_audit_contradiction
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    auditContradiction ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro auditBad
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_right representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      (ay_pece_disj_right coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))
        (ay_pece_disj_right staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))
          (ay_pece_disj_right uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))
            (ay_pece_disj_right buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)
              (ay_pece_disj_left auditContradiction inverseReconstructionGap
                auditBad))))))

theorem ay_pece_failure_inverse_reconstruction_gap
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop) :
    inverseReconstructionGap ->
    ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap := by
  intro mismatch
  exact ay_pece_disj_right classDrift
    (ay_pece_Disj representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))))
    (ay_pece_disj_right representativeLiteralMismatch
      (ay_pece_Disj coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))))
      (ay_pece_disj_right coverageGap
        (ay_pece_Disj staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))))
        (ay_pece_disj_right staleFingerprint
          (ay_pece_Disj uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)))
          (ay_pece_disj_right uncheckedReplay
            (ay_pece_Disj buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap))
            (ay_pece_disj_right buildDrift
              (ay_pece_Disj auditContradiction inverseReconstructionGap)
              (ay_pece_disj_right auditContradiction inverseReconstructionGap
                mismatch))))))

theorem ay_pece_diagnostic_no_claim
    (currentCnf : Prop)
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pece_DiagnosticEquivalenceClassEliminationReplay
      currentCnf classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap recompute diagnostic ->
    ay_pece_NoSemanticClaim diagnostic := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pece_NoSemanticClaim diagnostic)
    (fun _failure tail =>
      tail (ay_pece_NoSemanticClaim diagnostic)
        (fun _recompute noClaim => noClaim))

theorem ay_pece_diagnostic_recompute
    (currentCnf : Prop)
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pece_DiagnosticEquivalenceClassEliminationReplay
      currentCnf classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap recompute diagnostic ->
    ay_pece_RecomputeObligation currentCnf recompute := by
  intro diagnosticEntry
  exact diagnosticEntry (ay_pece_RecomputeObligation currentCnf recompute)
    (fun _failure tail =>
      tail (ay_pece_RecomputeObligation currentCnf recompute)
        (fun recomputeObligation _noClaim => recomputeObligation))

theorem ay_pece_unchecked_replay_cannot_bless_public_result
    (currentCnf : Prop)
    (classDrift : Prop) (representativeLiteralMismatch : Prop)
    (coverageGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (buildDrift : Prop)
    (auditContradiction : Prop) (inverseReconstructionGap : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_pece_RecomputeObligation currentCnf recompute ->
    ay_pece_NoSemanticClaim diagnostic ->
    ay_pece_DiagnosticEquivalenceClassEliminationReplay
      currentCnf classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap recompute diagnostic := by
  intro unchecked recomputeObligation noClaim
  exact ay_pece_conj_intro
    (ay_pece_EquivalenceClassFailure
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap)
    (ay_pece_Conj
      (ay_pece_RecomputeObligation currentCnf recompute)
      (ay_pece_NoSemanticClaim diagnostic))
    (ay_pece_failure_unchecked_replay
      classDrift representativeLiteralMismatch coverageGap staleFingerprint
      uncheckedReplay buildDrift auditContradiction inverseReconstructionGap unchecked)
    (ay_pece_conj_intro
      (ay_pece_RecomputeObligation currentCnf recompute)
      (ay_pece_NoSemanticClaim diagnostic)
      recomputeObligation noClaim)
