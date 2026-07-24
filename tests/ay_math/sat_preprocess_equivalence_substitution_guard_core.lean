-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalence-substitution preprocessing guard soundness.
-- The propositions stand for formula digests, equivalence-class ledgers,
-- representative-selection witnesses, substitution rewrite ledgers,
-- clause-origin maps, model/proof reconstruction, fallback/build/validator
-- gates, audit transcripts, diagnostics, and public SAT/UNSAT reports.

def ay_esubg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_esubg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_esubg_Equisat (original : Prop) (substituted : Prop) :=
  ay_esubg_Conj (original -> substituted) (substituted -> original)

def ay_esubg_Sat (cnf : Prop) (model : Prop) :=
  ay_esubg_Conj cnf model

def ay_esubg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_esubg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_esubg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_esubg_EquivalenceClassLedger
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop) :=
  ay_esubg_Conj classCoverage (classLedger -> classAccepted)

def ay_esubg_RepresentativeSelectionWitness
    (representativeWitness : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop) :=
  ay_esubg_Conj representativeCoverage
    (representativeWitness -> representativeAccepted)

def ay_esubg_SubstitutionRewriteLedger
    (rewriteLedger : Prop) (rewriteAccepted : Prop)
    (rewriteCoverage : Prop) :=
  ay_esubg_Conj rewriteCoverage (rewriteLedger -> rewriteAccepted)

def ay_esubg_ClauseOriginMap
    (originMap : Prop) (originAccepted : Prop)
    (originCoverage : Prop) :=
  ay_esubg_Conj originCoverage (originMap -> originAccepted)

def ay_esubg_ModelLiftWitness
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop) :=
  ay_esubg_Sat substitutedCnf substitutedModel ->
    ay_esubg_Sat originalCnf originalModel

def ay_esubg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (substitutedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_esubg_Replay substitutedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_esubg_ReconstructionWitnesses
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_esubg_Conj
    (ay_esubg_ModelLiftWitness
      substitutedCnf originalCnf substitutedModel originalModel)
    (ay_esubg_UnsatProofReconstructionWitness
      originalCnf substitutedCnf certificate conflict)

def ay_esubg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_esubg_Conj baselineSolver baselineAvailable

def ay_esubg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_esubg_Conj binaryFingerprint buildReproducible

def ay_esubg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_esubg_Conj validatorAccepted validatorVersion

def ay_esubg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_esubg_Conj auditAppended auditAppendOnly

def ay_esubg_AcceptedEquivalenceSubstitutionGuard
    (originalCnf : Prop) (substitutedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeWitness : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (rewriteLedger : Prop) (rewriteAccepted : Prop)
    (rewriteCoverage : Prop)
    (originMap : Prop) (originAccepted : Prop)
    (originCoverage : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_esubg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_esubg_EquivalenceClassLedger
       classLedger classAccepted classCoverage ->
     ay_esubg_RepresentativeSelectionWitness
       representativeWitness representativeAccepted representativeCoverage ->
     ay_esubg_SubstitutionRewriteLedger
       rewriteLedger rewriteAccepted rewriteCoverage ->
     ay_esubg_ClauseOriginMap
       originMap originAccepted originCoverage ->
     ay_esubg_ReconstructionWitnesses
       substitutedCnf originalCnf substitutedModel originalModel certificate conflict ->
     ay_esubg_Equisat originalCnf substitutedCnf ->
     ay_esubg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_esubg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_esubg_ValidatorGate validatorAccepted validatorVersion ->
     ay_esubg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_esubg_SubstitutionGuardFailure
    (digestMismatch : Prop) (classMismatch : Prop)
    (representativeMismatch : Prop) (rewriteMismatch : Prop)
    (originMismatch : Prop) (liftMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (classMismatch -> result) ->
    (representativeMismatch -> result) ->
    (rewriteMismatch -> result) ->
    (originMismatch -> result) ->
    (liftMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_esubg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_esubg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_esubg_Conj currentCnf recompute

def ay_esubg_DiagnosticSubstitutionGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (classMismatch : Prop)
    (representativeMismatch : Prop) (rewriteMismatch : Prop)
    (originMismatch : Prop) (liftMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_esubg_Conj
    (ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch)
    (ay_esubg_Conj
      (ay_esubg_RecomputeObligation currentCnf recompute)
      (ay_esubg_NoSemanticClaim diagnostic))

def ay_esubg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_esubg_Conj exitCode claim

def ay_esubg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_esubg_Disj
    (ay_esubg_ExitCodeSound exitCode (ay_esubg_Sat originalCnf model))
    (ay_esubg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_esubg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_esubg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_esubg_conj_left
    (left : Prop) (right : Prop) :
    ay_esubg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_esubg_conj_right
    (left : Prop) (right : Prop) :
    ay_esubg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_esubg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_esubg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_esubg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_esubg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_esubg_equisat_forward
    (original : Prop) (substituted : Prop) :
    ay_esubg_Equisat original substituted -> original -> substituted := by
  intro eqsat
  exact ay_esubg_conj_left (original -> substituted) (substituted -> original) eqsat

theorem ay_esubg_equisat_backward
    (original : Prop) (substituted : Prop) :
    ay_esubg_Equisat original substituted -> substituted -> original := by
  intro eqsat
  exact ay_esubg_conj_right (original -> substituted) (substituted -> original) eqsat

theorem ay_esubg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_esubg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_esubg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_esubg_equivalence_class_ledger_applies
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop) :
    ay_esubg_EquivalenceClassLedger
      classLedger classAccepted classCoverage ->
    classLedger -> classAccepted := by
  intro ledger
  exact ay_esubg_conj_right
    classCoverage (classLedger -> classAccepted) ledger

theorem ay_esubg_representative_selection_witness_applies
    (representativeWitness : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop) :
    ay_esubg_RepresentativeSelectionWitness
      representativeWitness representativeAccepted representativeCoverage ->
    representativeWitness -> representativeAccepted := by
  intro witness
  exact ay_esubg_conj_right
    representativeCoverage
    (representativeWitness -> representativeAccepted) witness

theorem ay_esubg_substitution_rewrite_ledger_applies
    (rewriteLedger : Prop) (rewriteAccepted : Prop)
    (rewriteCoverage : Prop) :
    ay_esubg_SubstitutionRewriteLedger
      rewriteLedger rewriteAccepted rewriteCoverage ->
    rewriteLedger -> rewriteAccepted := by
  intro ledger
  exact ay_esubg_conj_right
    rewriteCoverage (rewriteLedger -> rewriteAccepted) ledger

theorem ay_esubg_clause_origin_map_applies
    (originMap : Prop) (originAccepted : Prop)
    (originCoverage : Prop) :
    ay_esubg_ClauseOriginMap originMap originAccepted originCoverage ->
    originMap -> originAccepted := by
  intro map
  exact ay_esubg_conj_right
    originCoverage (originMap -> originAccepted) map

theorem ay_esubg_model_lift
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_esubg_ReconstructionWitnesses
      substitutedCnf originalCnf substitutedModel originalModel certificate conflict ->
    ay_esubg_Sat substitutedCnf substitutedModel ->
    ay_esubg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_esubg_conj_left
    (ay_esubg_ModelLiftWitness
      substitutedCnf originalCnf substitutedModel originalModel)
    (ay_esubg_UnsatProofReconstructionWitness
      originalCnf substitutedCnf certificate conflict)
    witnesses

theorem ay_esubg_unsat_proof_reconstruction
    (substitutedCnf : Prop) (originalCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_esubg_ReconstructionWitnesses
      substitutedCnf originalCnf substitutedModel originalModel certificate conflict ->
    ay_esubg_Replay substitutedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_esubg_conj_right
    (ay_esubg_ModelLiftWitness
      substitutedCnf originalCnf substitutedModel originalModel)
    (ay_esubg_UnsatProofReconstructionWitness
      originalCnf substitutedCnf certificate conflict)
    witnesses

theorem ay_esubg_accepted_equisat
    (originalCnf : Prop) (substitutedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeWitness : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (rewriteLedger : Prop) (rewriteAccepted : Prop)
    (rewriteCoverage : Prop)
    (originMap : Prop) (originAccepted : Prop)
    (originCoverage : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_esubg_AcceptedEquivalenceSubstitutionGuard
      originalCnf substitutedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      classLedger classAccepted classCoverage
      representativeWitness representativeAccepted representativeCoverage
      rewriteLedger rewriteAccepted rewriteCoverage
      originMap originAccepted originCoverage
      substitutedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_esubg_Equisat originalCnf substitutedCnf := by
  intro accepted
  exact accepted (ay_esubg_Equisat originalCnf substitutedCnf)
    (fun _digestOk _classOk _representativeOk _rewriteOk _originOk
      _reconstruct eqsat _fallback _build _validator _audit => eqsat)

theorem ay_esubg_accepted_reconstruction
    (originalCnf : Prop) (substitutedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeWitness : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (rewriteLedger : Prop) (rewriteAccepted : Prop)
    (rewriteCoverage : Prop)
    (originMap : Prop) (originAccepted : Prop)
    (originCoverage : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_esubg_AcceptedEquivalenceSubstitutionGuard
      originalCnf substitutedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      classLedger classAccepted classCoverage
      representativeWitness representativeAccepted representativeCoverage
      rewriteLedger rewriteAccepted rewriteCoverage
      originMap originAccepted originCoverage
      substitutedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_esubg_ReconstructionWitnesses
      substitutedCnf originalCnf substitutedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_esubg_ReconstructionWitnesses
      substitutedCnf originalCnf substitutedModel originalModel certificate conflict)
    (fun _digestOk _classOk _representativeOk _rewriteOk _originOk reconstruct
      _eqsat _fallback _build _validator _audit => reconstruct)

theorem ay_esubg_sat_pullback
    (originalCnf : Prop) (substitutedCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_esubg_ReconstructionWitnesses
      substitutedCnf originalCnf substitutedModel originalModel certificate conflict ->
    ay_esubg_Sat substitutedCnf substitutedModel ->
    ay_esubg_Sat originalCnf originalModel := by
  intro witnesses satSubstituted
  exact ay_esubg_model_lift
    substitutedCnf originalCnf substitutedModel originalModel
    certificate conflict witnesses satSubstituted

theorem ay_esubg_unsat_pushback
    (originalCnf : Prop) (substitutedCnf : Prop)
    (substitutedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_esubg_ReconstructionWitnesses
      substitutedCnf originalCnf substitutedModel originalModel certificate conflict ->
    ay_esubg_Replay substitutedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_esubg_unsat_proof_reconstruction
    substitutedCnf originalCnf substitutedModel originalModel
    certificate conflict witnesses replay

theorem ay_esubg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_esubg_ExitCodeSound exitCode (ay_esubg_Sat originalCnf originalModel) ->
    ay_esubg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_esubg_disj_left
    (ay_esubg_ExitCodeSound exitCode (ay_esubg_Sat originalCnf originalModel))
    (ay_esubg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_esubg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_esubg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_esubg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_esubg_disj_right
    (ay_esubg_ExitCodeSound exitCode (ay_esubg_Sat originalCnf originalModel))
    (ay_esubg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_esubg_failure_digest
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    digestMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result digest_case _class_case _representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_esubg_failure_class
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    classMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case class_case _representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact class_case h

theorem ay_esubg_failure_representative
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    representativeMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact representative_case h

theorem ay_esubg_failure_rewrite
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    rewriteMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact rewrite_case h

theorem ay_esubg_failure_origin
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    originMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    origin_case _lift_case _reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact origin_case h

theorem ay_esubg_failure_lift
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    liftMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    _origin_case lift_case _reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact lift_case h

theorem ay_esubg_failure_reconstruction
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    _origin_case _lift_case reconstruction_case _baseline_case
    _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_esubg_failure_baseline
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    baselineMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case baseline_case
    _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_esubg_failure_build
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    build_case _validator_case _audit_case
  exact build_case h

theorem ay_esubg_failure_validator
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    _build_case validator_case _audit_case
  exact validator_case h

theorem ay_esubg_failure_audit
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_esubg_SubstitutionGuardFailure
      digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch := by
  intro h result _digest_case _class_case _representative_case _rewrite_case
    _origin_case _lift_case _reconstruction_case _baseline_case
    _build_case _validator_case audit_case
  exact audit_case h

theorem ay_esubg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_esubg_DiagnosticSubstitutionGuard
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_esubg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_esubg_conj_right
    (ay_esubg_RecomputeObligation currentCnf recompute)
    (ay_esubg_NoSemanticClaim diagnostic)
    (ay_esubg_conj_right
      (ay_esubg_SubstitutionGuardFailure
        digestMismatch classMismatch representativeMismatch rewriteMismatch
        originMismatch liftMismatch reconstructionMismatch baselineMismatch
        buildMismatch validatorMismatch auditMismatch)
      (ay_esubg_Conj
        (ay_esubg_RecomputeObligation currentCnf recompute)
        (ay_esubg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_esubg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_esubg_DiagnosticSubstitutionGuard
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_esubg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_esubg_conj_left
    (ay_esubg_RecomputeObligation currentCnf recompute)
    (ay_esubg_NoSemanticClaim diagnostic)
    (ay_esubg_conj_right
      (ay_esubg_SubstitutionGuardFailure
        digestMismatch classMismatch representativeMismatch rewriteMismatch
        originMismatch liftMismatch reconstructionMismatch baselineMismatch
        buildMismatch validatorMismatch auditMismatch)
      (ay_esubg_Conj
        (ay_esubg_RecomputeObligation currentCnf recompute)
        (ay_esubg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_esubg_failed_substitution_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_esubg_DiagnosticSubstitutionGuard
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_esubg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_esubg_Conj
      (ay_esubg_NoSemanticClaim diagnostic)
      (ay_esubg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_esubg_conj_intro
    (ay_esubg_NoSemanticClaim diagnostic)
    (ay_esubg_RecomputeObligation currentCnf recompute)
    (ay_esubg_diagnostic_no_claim
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic diagnosticGuard)
    (ay_esubg_diagnostic_recompute
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic diagnosticGuard)

theorem ay_esubg_failed_substitution_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_esubg_DiagnosticSubstitutionGuard
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_esubg_ExitCodeSound exitCode (ay_esubg_Sat originalCnf model) ->
    ay_esubg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_esubg_diagnostic_no_claim
    currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
    originMismatch liftMismatch reconstructionMismatch baselineMismatch
    buildMismatch validatorMismatch auditMismatch
    recompute diagnostic diagnosticGuard

theorem ay_esubg_failed_substitution_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch classMismatch representativeMismatch rewriteMismatch : Prop)
    (originMismatch liftMismatch reconstructionMismatch baselineMismatch : Prop)
    (buildMismatch validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_esubg_DiagnosticSubstitutionGuard
      currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
      originMismatch liftMismatch reconstructionMismatch baselineMismatch
      buildMismatch validatorMismatch auditMismatch
      recompute diagnostic ->
    ay_esubg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_esubg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_esubg_diagnostic_no_claim
    currentCnf digestMismatch classMismatch representativeMismatch rewriteMismatch
    originMismatch liftMismatch reconstructionMismatch baselineMismatch
    buildMismatch validatorMismatch auditMismatch
    recompute diagnostic diagnosticGuard
