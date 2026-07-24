-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Definition-sharing guard soundness.
-- The propositions stand for definition table digests, shared-subformula coverage ledgers, representative
-- definition witnesses, auxiliary-variable domain manifests, reconstruction witnesses, fingerprint agreement, checker replay,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_dsgg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dsgg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_dsgg_Equisat (before : Prop) (after : Prop) :=
  ay_dsgg_Conj (before -> after) (after -> before)

def ay_dsgg_Sat (cnf : Prop) (model : Prop) :=
  ay_dsgg_Conj cnf model

def ay_dsgg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_dsgg_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_dsgg_Conj (leftId -> rightId) (rightId -> leftId)

def ay_dsgg_DefinitionTableDigest
    (definitionTable : Prop) (definitionTableAccepted : Prop)
    (definitionTableManifest : Prop) :=
  ay_dsgg_Conj definitionTableManifest (definitionTable -> definitionTableAccepted)

def ay_dsgg_SharedSubformulaCoverageLedger
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop)
    (sharedSubformulaCoverageWitness : Prop) :=
  ay_dsgg_Conj sharedSubformulaCoverageWitness (sharedSubformulaCoverage -> coverageAccepted)

def ay_dsgg_RepresentativeDefinitionWitness
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop)
    (representativeDefinitionManifest : Prop) :=
  ay_dsgg_Conj representativeDefinitionManifest (representativeDefinition -> representativeDefinitionAccepted)

def ay_dsgg_AuxiliaryVariableDomainManifest
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop) :=
  ay_dsgg_Conj auxiliaryDomainDigest (auxiliaryDomain -> auxiliaryDomainAccepted)

def ay_dsgg_ModelProjectionReconstruction
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :=
  ay_dsgg_Sat replayedCnf replayedModel ->
    ay_dsgg_Sat originalCnf originalModel

def ay_dsgg_ProofReconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_dsgg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_dsgg_ReconstructionWitnesses
    (replayedCnf : Prop) (originalCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_dsgg_Conj
    (ay_dsgg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_dsgg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)

def ay_dsgg_FingerprintAgreement
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_dsgg_Conj fingerprintWitness
    (ay_dsgg_IdMatch originalFingerprint replayedFingerprint)

def ay_dsgg_CheckerReplay
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop) :=
  ay_dsgg_Conj definitionSharingReplayCertificate checkerAccepted

def ay_dsgg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_dsgg_Conj baselineSolver baselineAvailable

def ay_dsgg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_dsgg_Conj binaryFingerprint buildReproducible

def ay_dsgg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_dsgg_Conj validatorAccepted validatorVersion

def ay_dsgg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_dsgg_Conj auditAppended auditAppendOnly

def ay_dsgg_AcceptedDefinitionSharingGuard
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_dsgg_DefinitionTableDigest
       definitionTable definitionTableAccepted definitionTableManifest ->
     ay_dsgg_SharedSubformulaCoverageLedger
       sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness ->
     ay_dsgg_RepresentativeDefinitionWitness
       representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest ->
     ay_dsgg_AuxiliaryVariableDomainManifest
       auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest ->
     ay_dsgg_ReconstructionWitnesses
       replayedCnf originalCnf replayedModel originalModel
       certificate conflict ->
     ay_dsgg_Equisat originalCnf replayedCnf ->
     ay_dsgg_FingerprintAgreement
       originalFingerprint replayedFingerprint fingerprintWitness ->
     ay_dsgg_CheckerReplay definitionSharingReplayCertificate checkerAccepted ->
     ay_dsgg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_dsgg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_dsgg_ValidatorGate validatorAccepted validatorVersion ->
     ay_dsgg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_dsgg_DefinitionSharingGuardFailure
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :=
  forall result : Prop,
    (staleDefinitionTableDigest -> result) ->
    (coverageLedgerMismatch -> result) ->
    (representativeDefinitionMismatch -> result) ->
    (auxiliaryDomainGap -> result) ->
    (reconstructionGap -> result) ->
    (staleFingerprint -> result) ->
    (uncheckedReplay -> result) ->
    (missingBaseline -> result) ->
    (buildDrift -> result) ->
    (validatorFailure -> result) ->
    (auditContradiction -> result) ->
    result

def ay_dsgg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_dsgg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_dsgg_Conj currentCnf recompute

def ay_dsgg_DiagnosticDefinitionSharingGuard
    (currentCnf : Prop)
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_dsgg_Conj
    (ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap
      reconstructionGap staleFingerprint uncheckedReplay missingBaseline
      buildDrift validatorFailure
      auditContradiction)
    (ay_dsgg_Conj
      (ay_dsgg_RecomputeObligation currentCnf recompute)
      (ay_dsgg_NoSemanticClaim diagnostic))

def ay_dsgg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_dsgg_Conj exitCode claim

def ay_dsgg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_dsgg_Disj
    (ay_dsgg_ExitCodeSound exitCode (ay_dsgg_Sat originalCnf model))
    (ay_dsgg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_dsgg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_dsgg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_dsgg_conj_left
    (left : Prop) (right : Prop) :
    ay_dsgg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_dsgg_conj_right
    (left : Prop) (right : Prop) :
    ay_dsgg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_dsgg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_dsgg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_dsgg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_dsgg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_dsgg_equisat_forward
    (before : Prop) (after : Prop) :
    ay_dsgg_Equisat before after ->
    before -> after := by
  intro eqsat
  exact ay_dsgg_conj_left (before -> after) (after -> before) eqsat

theorem ay_dsgg_equisat_backward
    (before : Prop) (after : Prop) :
    ay_dsgg_Equisat before after ->
    after -> before := by
  intro eqsat
  exact ay_dsgg_conj_right (before -> after) (after -> before) eqsat

theorem ay_dsgg_definition_table_digest_applies
    (definitionTable : Prop) (definitionTableAccepted : Prop)
    (definitionTableManifest : Prop) :
    ay_dsgg_DefinitionTableDigest
      definitionTable definitionTableAccepted definitionTableManifest ->
    definitionTable -> definitionTableAccepted := by
  intro digest
  exact ay_dsgg_conj_right definitionTableManifest
    (definitionTable -> definitionTableAccepted) digest

theorem ay_dsgg_shared_subformula_coverage_ledger_applies
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop)
    (sharedSubformulaCoverageWitness : Prop) :
    ay_dsgg_SharedSubformulaCoverageLedger
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness ->
    sharedSubformulaCoverage -> coverageAccepted := by
  intro digest
  exact ay_dsgg_conj_right sharedSubformulaCoverageWitness
    (sharedSubformulaCoverage -> coverageAccepted) digest

theorem ay_dsgg_representative_definition_witness_applies
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop)
    (representativeDefinitionManifest : Prop) :
    ay_dsgg_RepresentativeDefinitionWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest ->
    representativeDefinition -> representativeDefinitionAccepted := by
  intro ledger
  exact ay_dsgg_conj_right representativeDefinitionManifest
    (representativeDefinition -> representativeDefinitionAccepted) ledger

theorem ay_dsgg_auxiliary_variable_domain_manifest_applies
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop) :
    ay_dsgg_AuxiliaryVariableDomainManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest ->
    auxiliaryDomain -> auxiliaryDomainAccepted := by
  intro coverage
  exact ay_dsgg_conj_right auxiliaryDomainDigest
    (auxiliaryDomain -> auxiliaryDomainAccepted) coverage

theorem ay_dsgg_model_projection_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_dsgg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_dsgg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel := by
  intro witnesses
  exact ay_dsgg_conj_left
    (ay_dsgg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_dsgg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_dsgg_proof_reconstruction
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_dsgg_ReconstructionWitnesses
      replayedCnf originalCnf replayedModel originalModel
      certificate conflict ->
    ay_dsgg_ProofReconstruction
      originalCnf replayedCnf certificate conflict := by
  intro witnesses
  exact ay_dsgg_conj_right
    (ay_dsgg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel)
    (ay_dsgg_ProofReconstruction
      originalCnf replayedCnf certificate conflict)
    witnesses

theorem ay_dsgg_accepted_equisat
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_dsgg_AcceptedDefinitionSharingGuard
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_dsgg_Equisat originalCnf replayedCnf := by
  intro accepted
  exact accepted (ay_dsgg_Equisat originalCnf replayedCnf)
    (fun _manifest _schema _auxiliary _coverage _reconstruct eqsat _coverage _checker
      _fallback _build _validator _audit => eqsat)

theorem ay_dsgg_accepted_forward_map
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_dsgg_AcceptedDefinitionSharingGuard
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    originalCnf -> replayedCnf := by
  intro accepted
  exact ay_dsgg_equisat_forward originalCnf replayedCnf
    (ay_dsgg_accepted_equisat
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly
      accepted)

theorem ay_dsgg_accepted_checker_replay
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_dsgg_AcceptedDefinitionSharingGuard
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_dsgg_CheckerReplay definitionSharingReplayCertificate checkerAccepted := by
  intro accepted
  exact accepted (ay_dsgg_CheckerReplay definitionSharingReplayCertificate checkerAccepted)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage checker
      _fallback _build _validator _audit => checker)

theorem ay_dsgg_accepted_audit_transcript
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_dsgg_AcceptedDefinitionSharingGuard
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_dsgg_AuditTranscript auditAppended auditAppendOnly := by
  intro accepted
  exact accepted (ay_dsgg_AuditTranscript auditAppended auditAppendOnly)
    (fun _manifest _schema _auxiliary _coverage _reconstruct _eqsat _coverage _checker
      _fallback _build _validator audit => audit)

theorem ay_dsgg_sat_pullback
    (originalCnf : Prop) (replayedCnf : Prop)
    (replayedModel : Prop) (originalModel : Prop) :
    ay_dsgg_ModelProjectionReconstruction
      replayedCnf originalCnf replayedModel originalModel ->
    ay_dsgg_Sat replayedCnf replayedModel ->
    ay_dsgg_Sat originalCnf originalModel := by
  intro reconstruct replayedSat
  exact reconstruct replayedSat

theorem ay_dsgg_unsat_pushback
    (originalCnf : Prop) (replayedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_dsgg_ProofReconstruction
      originalCnf replayedCnf certificate conflict ->
    ay_dsgg_Replay replayedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro reconstruct replayedReplay
  exact reconstruct replayedReplay

theorem ay_dsgg_public_sat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_dsgg_AcceptedDefinitionSharingGuard
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_dsgg_Sat replayedCnf replayedModel ->
    exitCode ->
    ay_dsgg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedSat hexit
  exact accepted
    (ay_dsgg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_dsgg_disj_left
        (ay_dsgg_ExitCodeSound exitCode
          (ay_dsgg_Sat originalCnf originalModel))
        (ay_dsgg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_dsgg_conj_intro exitCode
          (ay_dsgg_Sat originalCnf originalModel)
          hexit
          ((ay_dsgg_model_projection_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedSat)))

theorem ay_dsgg_public_unsat_sound
    (originalCnf : Prop) (replayedCnf : Prop)
    (definitionTable : Prop) (definitionTableAccepted : Prop) (definitionTableManifest : Prop)
    (sharedSubformulaCoverage : Prop) (coverageAccepted : Prop) (sharedSubformulaCoverageWitness : Prop)
    (representativeDefinition : Prop) (representativeDefinitionAccepted : Prop) (representativeDefinitionManifest : Prop)
    (auxiliaryDomain : Prop) (auxiliaryDomainAccepted : Prop)
    (auxiliaryDomainDigest : Prop)
    (replayedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (replayedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (definitionSharingReplayCertificate : Prop) (checkerAccepted : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop)
    (exitCode : Prop) :
    ay_dsgg_AcceptedDefinitionSharingGuard
      originalCnf replayedCnf
      definitionTable definitionTableAccepted definitionTableManifest
      sharedSubformulaCoverage coverageAccepted sharedSubformulaCoverageWitness
      representativeDefinition representativeDefinitionAccepted representativeDefinitionManifest
      auxiliaryDomain auxiliaryDomainAccepted auxiliaryDomainDigest
      replayedModel originalModel certificate conflict
      originalFingerprint replayedFingerprint fingerprintWitness
      definitionSharingReplayCertificate checkerAccepted
      baselineSolver baselineAvailable binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_dsgg_Replay replayedCnf certificate conflict ->
    exitCode ->
    ay_dsgg_PublicResult
      originalCnf originalModel certificate conflict exitCode := by
  intro accepted replayedReplay hexit
  exact accepted
    (ay_dsgg_PublicResult
      originalCnf originalModel certificate conflict exitCode)
    (fun _manifest _schema _auxiliary _coverage reconstruct _eqsat _coverage _checker
      _fallback _build _validator _audit =>
      ay_dsgg_disj_right
        (ay_dsgg_ExitCodeSound exitCode
          (ay_dsgg_Sat originalCnf originalModel))
        (ay_dsgg_ExitCodeSound exitCode
          (certificate -> originalCnf -> conflict))
        (ay_dsgg_conj_intro exitCode
          (certificate -> originalCnf -> conflict)
          hexit
          ((ay_dsgg_proof_reconstruction
            originalCnf replayedCnf replayedModel originalModel
            certificate conflict reconstruct) replayedReplay)))

theorem ay_dsgg_failure_stale_definition_table_digest
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleDefinitionTableDigest ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result constraint_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact constraint_case failure

theorem ay_dsgg_failure_shared_subformula_coverage_ledger
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    coverageLedgerMismatch ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case schema_case _auxiliary_case _coverage_case
    _reconstruction_case _coverage_case _schema_case _baseline_case
    _build_case _validator_case _audit_case
  exact schema_case failure

theorem ay_dsgg_failure_representative_definition_witness
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    representativeDefinitionMismatch ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_dsgg_failure_auxiliary_variable_domain
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auxiliaryDomainGap ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case auxiliary_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact auxiliary_case failure

theorem ay_dsgg_failure_reconstruction
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    reconstructionGap ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact reconstruction_case failure

theorem ay_dsgg_failure_stale_fingerprint
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    staleFingerprint ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    fingerprint_case _schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact fingerprint_case failure

theorem ay_dsgg_failure_unchecked_replay
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    uncheckedReplay ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case schema_case _baseline_case _build_case
    _validator_case _audit_case
  exact schema_case failure

theorem ay_dsgg_failure_missing_baseline
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    missingBaseline ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case baseline_case _build_case
    _validator_case _audit_case
  exact baseline_case failure

theorem ay_dsgg_failure_build
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    buildDrift ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case build_case
    _validator_case _audit_case
  exact build_case failure

theorem ay_dsgg_failure_validator
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    validatorFailure ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    validator_case _audit_case
  exact validator_case failure

theorem ay_dsgg_failure_audit
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop) :
    auditContradiction ->
    ay_dsgg_DefinitionSharingGuardFailure
      staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
      uncheckedReplay missingBaseline buildDrift validatorFailure
      auditContradiction := by
  intro failure result _manifest_case _schema_case _auxiliary_case _coverage_case _reconstruction_case
    _coverage_case _schema_case _baseline_case _build_case
    _validator_case audit_case
  exact audit_case failure

theorem ay_dsgg_diagnostic_no_claim
    (currentCnf : Prop)
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_dsgg_DiagnosticDefinitionSharingGuard
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_dsgg_NoSemanticClaim diagnostic := by
  intro diagnosticBundle
  exact ay_dsgg_conj_right
    (ay_dsgg_RecomputeObligation currentCnf recompute)
    (ay_dsgg_NoSemanticClaim diagnostic)
    (ay_dsgg_conj_right
      (ay_dsgg_DefinitionSharingGuardFailure
        staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_dsgg_Conj
        (ay_dsgg_RecomputeObligation currentCnf recompute)
        (ay_dsgg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_dsgg_diagnostic_recompute
    (currentCnf : Prop)
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_dsgg_DiagnosticDefinitionSharingGuard
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_dsgg_RecomputeObligation currentCnf recompute := by
  intro diagnosticBundle
  exact ay_dsgg_conj_left
    (ay_dsgg_RecomputeObligation currentCnf recompute)
    (ay_dsgg_NoSemanticClaim diagnostic)
    (ay_dsgg_conj_right
      (ay_dsgg_DefinitionSharingGuardFailure
        staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap staleFingerprint
        uncheckedReplay missingBaseline buildDrift validatorFailure
        auditContradiction)
      (ay_dsgg_Conj
        (ay_dsgg_RecomputeObligation currentCnf recompute)
        (ay_dsgg_NoSemanticClaim diagnostic))
      diagnosticBundle)

theorem ay_dsgg_unchecked_definition_sharing_cannot_bless_public_result
    (currentCnf : Prop)
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_dsgg_DiagnosticDefinitionSharingGuard
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_dsgg_Conj
      (ay_dsgg_NoSemanticClaim diagnostic)
      (ay_dsgg_RecomputeObligation currentCnf recompute) := by
  intro _unchecked diagnosticBundle
  exact ay_dsgg_conj_intro
    (ay_dsgg_NoSemanticClaim diagnostic)
    (ay_dsgg_RecomputeObligation currentCnf recompute)
    (ay_dsgg_diagnostic_no_claim
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)
    (ay_dsgg_diagnostic_recompute
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic diagnosticBundle)

theorem ay_dsgg_unchecked_definition_sharing_cannot_bless_public_sat
    (currentCnf : Prop)
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_dsgg_DiagnosticDefinitionSharingGuard
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_dsgg_NoSemanticClaim diagnostic := by
  intro _unchecked diagnosticBundle
  exact ay_dsgg_diagnostic_no_claim
    currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle

theorem ay_dsgg_unchecked_definition_sharing_cannot_bless_public_unsat
    (currentCnf : Prop)
    (staleDefinitionTableDigest : Prop) (coverageLedgerMismatch : Prop)
    (representativeDefinitionMismatch : Prop)
    (auxiliaryDomainGap : Prop)
    (reconstructionGap : Prop) (staleFingerprint : Prop)
    (uncheckedReplay : Prop) (missingBaseline : Prop)
    (buildDrift : Prop) (validatorFailure : Prop)
    (auditContradiction : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    uncheckedReplay ->
    ay_dsgg_DiagnosticDefinitionSharingGuard
      currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
      staleFingerprint uncheckedReplay missingBaseline buildDrift
      validatorFailure auditContradiction recompute diagnostic ->
    ay_dsgg_RecomputeObligation currentCnf recompute := by
  intro _unchecked diagnosticBundle
  exact ay_dsgg_diagnostic_recompute
    currentCnf staleDefinitionTableDigest coverageLedgerMismatch representativeDefinitionMismatch auxiliaryDomainGap reconstructionGap
    staleFingerprint uncheckedReplay missingBaseline buildDrift
    validatorFailure auditContradiction recompute diagnostic diagnosticBundle
