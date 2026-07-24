-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalence-class substitution preprocessing guard soundness.
-- The propositions stand for original formula fingerprints, equivalence-class
-- ledgers, representative-choice manifests, substitution map digests,
-- rewritten formula digests, per-equivalence proof/equisat witnesses, model
-- reconstruction, UNSAT replay/equisat evidence, build/validator gates,
-- fallback no-claim paths, audit transcripts, and public SAT/UNSAT reports.

def ay_ecsg2_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ecsg2_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ecsg2_Equisat (original : Prop) (rewritten : Prop) :=
  ay_ecsg2_Conj (original -> rewritten) (rewritten -> original)

def ay_ecsg2_Sat (cnf : Prop) (model : Prop) :=
  ay_ecsg2_Conj cnf model

def ay_ecsg2_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ecsg2_OriginalFormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_ecsg2_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_ecsg2_EquivalenceClassLedger
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop) :=
  ay_ecsg2_Conj classCoverage (classLedger -> classAccepted)

def ay_ecsg2_RepresentativeChoiceManifest
    (representativeManifest : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop) :=
  ay_ecsg2_Conj representativeCoverage
    (representativeManifest -> representativeAccepted)

def ay_ecsg2_SubstitutionMapDigest
    (substitutionMapDigest : Prop) (substitutionDigestAccepted : Prop)
    (substitutionDigestManifest : Prop) :=
  ay_ecsg2_Conj substitutionDigestManifest
    (substitutionMapDigest -> substitutionDigestAccepted)

def ay_ecsg2_RewrittenFormulaDigest
    (rewrittenFormulaDigest : Prop) (rewriteDigestAccepted : Prop)
    (rewriteDigestManifest : Prop) :=
  ay_ecsg2_Conj rewriteDigestManifest
    (rewrittenFormulaDigest -> rewriteDigestAccepted)

def ay_ecsg2_PerEquivalenceProofWitness
    (equivalenceProofWitness : Prop) (equivalenceProofAccepted : Prop)
    (equivalenceProofCoverage : Prop) :=
  ay_ecsg2_Conj equivalenceProofCoverage
    (equivalenceProofWitness -> equivalenceProofAccepted)

def ay_ecsg2_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_ecsg2_Conj checkerAccepted
    (ay_ecsg2_Conj validatorAccepted validatorVersion)

def ay_ecsg2_ModelReconstructionWitness
    (rewrittenCnf : Prop) (originalCnf : Prop)
    (representativeModel : Prop) (originalModel : Prop) :=
  ay_ecsg2_Sat rewrittenCnf representativeModel ->
    ay_ecsg2_Sat originalCnf originalModel

def ay_ecsg2_UnsatReplayEquisatWitness
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ecsg2_Replay rewrittenCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_ecsg2_ReconstructionEvidence
    (rewrittenCnf : Prop) (originalCnf : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ecsg2_Conj
    (ay_ecsg2_ModelReconstructionWitness
      rewrittenCnf originalCnf representativeModel originalModel)
    (ay_ecsg2_UnsatReplayEquisatWitness
      originalCnf rewrittenCnf certificate conflict)

def ay_ecsg2_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_ecsg2_Conj binaryFingerprint buildReproducible

def ay_ecsg2_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_ecsg2_Conj baselineAvailable noClaimPath

def ay_ecsg2_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_ecsg2_Conj auditAppended auditAppendOnly

def ay_ecsg2_AcceptedEquivalenceClassSubstitutionGuard
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeManifest : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (substitutionMapDigest : Prop) (substitutionDigestAccepted : Prop)
    (substitutionDigestManifest : Prop)
    (rewrittenFormulaDigest : Prop) (rewriteDigestAccepted : Prop)
    (rewriteDigestManifest : Prop)
    (equivalenceProofWitness : Prop) (equivalenceProofAccepted : Prop)
    (equivalenceProofCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_ecsg2_OriginalFormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_ecsg2_EquivalenceClassLedger classLedger classAccepted classCoverage ->
     ay_ecsg2_RepresentativeChoiceManifest
       representativeManifest representativeAccepted representativeCoverage ->
     ay_ecsg2_SubstitutionMapDigest
       substitutionMapDigest substitutionDigestAccepted substitutionDigestManifest ->
     ay_ecsg2_RewrittenFormulaDigest
       rewrittenFormulaDigest rewriteDigestAccepted rewriteDigestManifest ->
     ay_ecsg2_PerEquivalenceProofWitness
       equivalenceProofWitness equivalenceProofAccepted equivalenceProofCoverage ->
     ay_ecsg2_ReconstructionEvidence
       rewrittenCnf originalCnf representativeModel originalModel certificate conflict ->
     ay_ecsg2_Equisat originalCnf rewrittenCnf ->
     ay_ecsg2_BuildEvidence binaryFingerprint buildReproducible ->
     ay_ecsg2_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_ecsg2_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_ecsg2_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_ecsg2_SubstitutionGuardFailure
    (classMismatch : Prop) (representativeMismatch : Prop)
    (substitutionMismatch : Prop) (rewriteMismatch : Prop)
    (equivalenceMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (classMismatch -> result) ->
    (representativeMismatch -> result) ->
    (substitutionMismatch -> result) ->
    (rewriteMismatch -> result) ->
    (equivalenceMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ecsg2_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ecsg2_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_ecsg2_Conj currentCnf recompute

def ay_ecsg2_DiagnosticSubstitutionGuard
    (currentCnf : Prop)
    (classMismatch : Prop) (representativeMismatch : Prop)
    (substitutionMismatch : Prop) (rewriteMismatch : Prop)
    (equivalenceMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ecsg2_Conj
    (ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_ecsg2_Conj
      (ay_ecsg2_RecomputeObligation currentCnf recompute)
      (ay_ecsg2_NoSemanticClaim diagnostic))

def ay_ecsg2_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ecsg2_Conj exitCode claim

def ay_ecsg2_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ecsg2_Disj
    (ay_ecsg2_ExitCodeSound exitCode (ay_ecsg2_Sat originalCnf model))
    (ay_ecsg2_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_ecsg2_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ecsg2_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ecsg2_conj_left
    (left : Prop) (right : Prop) :
    ay_ecsg2_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ecsg2_conj_right
    (left : Prop) (right : Prop) :
    ay_ecsg2_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ecsg2_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ecsg2_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ecsg2_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ecsg2_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ecsg2_equisat_forward
    (original : Prop) (rewritten : Prop) :
    ay_ecsg2_Equisat original rewritten -> original -> rewritten := by
  intro eqsat
  exact ay_ecsg2_conj_left (original -> rewritten) (rewritten -> original) eqsat

theorem ay_ecsg2_equisat_backward
    (original : Prop) (rewritten : Prop) :
    ay_ecsg2_Equisat original rewritten -> rewritten -> original := by
  intro eqsat
  exact ay_ecsg2_conj_right (original -> rewritten) (rewritten -> original) eqsat

theorem ay_ecsg2_class_ledger_applies
    (classLedger : Prop) (classAccepted : Prop) (classCoverage : Prop) :
    ay_ecsg2_EquivalenceClassLedger classLedger classAccepted classCoverage ->
    classLedger -> classAccepted := by
  intro ledger
  exact ay_ecsg2_conj_right classCoverage (classLedger -> classAccepted) ledger

theorem ay_ecsg2_representative_manifest_applies
    (representativeManifest : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop) :
    ay_ecsg2_RepresentativeChoiceManifest
      representativeManifest representativeAccepted representativeCoverage ->
    representativeManifest -> representativeAccepted := by
  intro manifest
  exact ay_ecsg2_conj_right
    representativeCoverage (representativeManifest -> representativeAccepted)
    manifest

theorem ay_ecsg2_substitution_digest_applies
    (substitutionMapDigest : Prop) (substitutionDigestAccepted : Prop)
    (substitutionDigestManifest : Prop) :
    ay_ecsg2_SubstitutionMapDigest
      substitutionMapDigest substitutionDigestAccepted substitutionDigestManifest ->
    substitutionMapDigest -> substitutionDigestAccepted := by
  intro digest
  exact ay_ecsg2_conj_right
    substitutionDigestManifest
    (substitutionMapDigest -> substitutionDigestAccepted)
    digest

theorem ay_ecsg2_rewrite_digest_applies
    (rewrittenFormulaDigest : Prop) (rewriteDigestAccepted : Prop)
    (rewriteDigestManifest : Prop) :
    ay_ecsg2_RewrittenFormulaDigest
      rewrittenFormulaDigest rewriteDigestAccepted rewriteDigestManifest ->
    rewrittenFormulaDigest -> rewriteDigestAccepted := by
  intro digest
  exact ay_ecsg2_conj_right
    rewriteDigestManifest (rewrittenFormulaDigest -> rewriteDigestAccepted)
    digest

theorem ay_ecsg2_equivalence_witness_applies
    (equivalenceProofWitness : Prop) (equivalenceProofAccepted : Prop)
    (equivalenceProofCoverage : Prop) :
    ay_ecsg2_PerEquivalenceProofWitness
      equivalenceProofWitness equivalenceProofAccepted equivalenceProofCoverage ->
    equivalenceProofWitness -> equivalenceProofAccepted := by
  intro witness
  exact ay_ecsg2_conj_right
    equivalenceProofCoverage
    (equivalenceProofWitness -> equivalenceProofAccepted)
    witness

theorem ay_ecsg2_model_reconstruction
    (rewrittenCnf : Prop) (originalCnf : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ecsg2_ReconstructionEvidence
      rewrittenCnf originalCnf representativeModel originalModel certificate conflict ->
    ay_ecsg2_Sat rewrittenCnf representativeModel ->
    ay_ecsg2_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_ecsg2_conj_left
    (ay_ecsg2_ModelReconstructionWitness
      rewrittenCnf originalCnf representativeModel originalModel)
    (ay_ecsg2_UnsatReplayEquisatWitness
      originalCnf rewrittenCnf certificate conflict)
    witnesses

theorem ay_ecsg2_unsat_replay
    (rewrittenCnf : Prop) (originalCnf : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ecsg2_ReconstructionEvidence
      rewrittenCnf originalCnf representativeModel originalModel certificate conflict ->
    ay_ecsg2_Replay rewrittenCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_ecsg2_conj_right
    (ay_ecsg2_ModelReconstructionWitness
      rewrittenCnf originalCnf representativeModel originalModel)
    (ay_ecsg2_UnsatReplayEquisatWitness
      originalCnf rewrittenCnf certificate conflict)
    witnesses

theorem ay_ecsg2_accepted_equisat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeManifest : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (substitutionMapDigest : Prop) (substitutionDigestAccepted : Prop)
    (substitutionDigestManifest : Prop)
    (rewrittenFormulaDigest : Prop) (rewriteDigestAccepted : Prop)
    (rewriteDigestManifest : Prop)
    (equivalenceProofWitness : Prop) (equivalenceProofAccepted : Prop)
    (equivalenceProofCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ecsg2_AcceptedEquivalenceClassSubstitutionGuard
      originalCnf rewrittenCnf
      fingerprint fingerprintAccepted fingerprintManifest
      classLedger classAccepted classCoverage
      representativeManifest representativeAccepted representativeCoverage
      substitutionMapDigest substitutionDigestAccepted substitutionDigestManifest
      rewrittenFormulaDigest rewriteDigestAccepted rewriteDigestManifest
      equivalenceProofWitness equivalenceProofAccepted equivalenceProofCoverage
      checkerAccepted validatorAccepted validatorVersion
      representativeModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_ecsg2_Equisat originalCnf rewrittenCnf := by
  intro accepted
  exact accepted (ay_ecsg2_Equisat originalCnf rewrittenCnf)
    (fun _fingerprint _class _representative _substitution _rewrite
      _equiv _reconstruct eqsat _build _validator _fallback _audit => eqsat)

theorem ay_ecsg2_accepted_reconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeManifest : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (substitutionMapDigest : Prop) (substitutionDigestAccepted : Prop)
    (substitutionDigestManifest : Prop)
    (rewrittenFormulaDigest : Prop) (rewriteDigestAccepted : Prop)
    (rewriteDigestManifest : Prop)
    (equivalenceProofWitness : Prop) (equivalenceProofAccepted : Prop)
    (equivalenceProofCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ecsg2_AcceptedEquivalenceClassSubstitutionGuard
      originalCnf rewrittenCnf
      fingerprint fingerprintAccepted fingerprintManifest
      classLedger classAccepted classCoverage
      representativeManifest representativeAccepted representativeCoverage
      substitutionMapDigest substitutionDigestAccepted substitutionDigestManifest
      rewrittenFormulaDigest rewriteDigestAccepted rewriteDigestManifest
      equivalenceProofWitness equivalenceProofAccepted equivalenceProofCoverage
      checkerAccepted validatorAccepted validatorVersion
      representativeModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_ecsg2_ReconstructionEvidence
      rewrittenCnf originalCnf representativeModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_ecsg2_ReconstructionEvidence
      rewrittenCnf originalCnf representativeModel originalModel certificate conflict)
    (fun _fingerprint _class _representative _substitution _rewrite
      _equiv reconstruct _eqsat _build _validator _fallback _audit =>
      reconstruct)

theorem ay_ecsg2_substitution_has_exact_equivalence
    (classLedger : Prop) (classAccepted : Prop)
    (classCoverage : Prop)
    (representativeManifest : Prop) (representativeAccepted : Prop)
    (representativeCoverage : Prop)
    (substitutionMapDigest : Prop) (substitutionDigestAccepted : Prop)
    (substitutionDigestManifest : Prop)
    (equivalenceProofWitness : Prop) (equivalenceProofAccepted : Prop)
    (equivalenceProofCoverage : Prop) :
    ay_ecsg2_EquivalenceClassLedger classLedger classAccepted classCoverage ->
    ay_ecsg2_RepresentativeChoiceManifest
      representativeManifest representativeAccepted representativeCoverage ->
    ay_ecsg2_SubstitutionMapDigest
      substitutionMapDigest substitutionDigestAccepted substitutionDigestManifest ->
    ay_ecsg2_PerEquivalenceProofWitness
      equivalenceProofWitness equivalenceProofAccepted equivalenceProofCoverage ->
    classLedger -> representativeManifest -> substitutionMapDigest ->
    equivalenceProofWitness ->
    forall result : Prop,
      (classAccepted -> representativeAccepted -> substitutionDigestAccepted ->
        equivalenceProofAccepted -> result) -> result := by
  intro classOk repOk substOk equivOk hClass hRepresentative hSubstitution hEquiv
  intro result build
  exact build
    (ay_ecsg2_class_ledger_applies
      classLedger classAccepted classCoverage classOk hClass)
    (ay_ecsg2_representative_manifest_applies
      representativeManifest representativeAccepted representativeCoverage
      repOk hRepresentative)
    (ay_ecsg2_substitution_digest_applies
      substitutionMapDigest substitutionDigestAccepted substitutionDigestManifest
      substOk hSubstitution)
    (ay_ecsg2_equivalence_witness_applies
      equivalenceProofWitness equivalenceProofAccepted equivalenceProofCoverage
      equivOk hEquiv)

theorem ay_ecsg2_sat_pullback
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ecsg2_ReconstructionEvidence
      rewrittenCnf originalCnf representativeModel originalModel certificate conflict ->
    ay_ecsg2_Sat rewrittenCnf representativeModel ->
    ay_ecsg2_Sat originalCnf originalModel := by
  intro witnesses satRewritten
  exact ay_ecsg2_model_reconstruction
    rewrittenCnf originalCnf representativeModel originalModel
    certificate conflict witnesses satRewritten

theorem ay_ecsg2_unsat_pushback
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (representativeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ecsg2_ReconstructionEvidence
      rewrittenCnf originalCnf representativeModel originalModel certificate conflict ->
    ay_ecsg2_Replay rewrittenCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_ecsg2_unsat_replay
    rewrittenCnf originalCnf representativeModel originalModel
    certificate conflict witnesses replay

theorem ay_ecsg2_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ecsg2_ExitCodeSound exitCode (ay_ecsg2_Sat originalCnf originalModel) ->
    ay_ecsg2_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_ecsg2_disj_left
    (ay_ecsg2_ExitCodeSound exitCode (ay_ecsg2_Sat originalCnf originalModel))
    (ay_ecsg2_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_ecsg2_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ecsg2_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ecsg2_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_ecsg2_disj_right
    (ay_ecsg2_ExitCodeSound exitCode (ay_ecsg2_Sat originalCnf originalModel))
    (ay_ecsg2_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_ecsg2_failure_class
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    classMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result class_case _rep_case _subst_case _rewrite_case _equiv_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact class_case h

theorem ay_ecsg2_failure_representative
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    representativeMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case rep_case _subst_case _rewrite_case _equiv_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact rep_case h

theorem ay_ecsg2_failure_substitution
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    substitutionMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case subst_case _rewrite_case _equiv_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact subst_case h

theorem ay_ecsg2_failure_rewrite
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    rewriteMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case rewrite_case _equiv_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact rewrite_case h

theorem ay_ecsg2_failure_equivalence
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    equivalenceMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case _rewrite_case equiv_case
    _model_case _replay_case _build_case _validator_case _audit_case
  exact equiv_case h

theorem ay_ecsg2_failure_model
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    modelMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case _rewrite_case _equiv_case
    model_case _replay_case _build_case _validator_case _audit_case
  exact model_case h

theorem ay_ecsg2_failure_replay
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case _rewrite_case _equiv_case
    _model_case replay_case _build_case _validator_case _audit_case
  exact replay_case h

theorem ay_ecsg2_failure_build
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case _rewrite_case _equiv_case
    _model_case _replay_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_ecsg2_failure_validator
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case _rewrite_case _equiv_case
    _model_case _replay_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_ecsg2_failure_audit
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_ecsg2_SubstitutionGuardFailure
      classMismatch representativeMismatch substitutionMismatch rewriteMismatch
      equivalenceMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _class_case _rep_case _subst_case _rewrite_case _equiv_case
    _model_case _replay_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_ecsg2_diagnostic_no_claim
    (currentCnf : Prop)
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ecsg2_DiagnosticSubstitutionGuard
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_ecsg2_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_ecsg2_conj_right
    (ay_ecsg2_RecomputeObligation currentCnf recompute)
    (ay_ecsg2_NoSemanticClaim diagnostic)
    (ay_ecsg2_conj_right
      (ay_ecsg2_SubstitutionGuardFailure
        classMismatch representativeMismatch substitutionMismatch rewriteMismatch
        equivalenceMismatch modelMismatch replayMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_ecsg2_Conj
        (ay_ecsg2_RecomputeObligation currentCnf recompute)
        (ay_ecsg2_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ecsg2_diagnostic_recompute
    (currentCnf : Prop)
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ecsg2_DiagnosticSubstitutionGuard
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_ecsg2_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_ecsg2_conj_left
    (ay_ecsg2_RecomputeObligation currentCnf recompute)
    (ay_ecsg2_NoSemanticClaim diagnostic)
    (ay_ecsg2_conj_right
      (ay_ecsg2_SubstitutionGuardFailure
        classMismatch representativeMismatch substitutionMismatch rewriteMismatch
        equivalenceMismatch modelMismatch replayMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_ecsg2_Conj
        (ay_ecsg2_RecomputeObligation currentCnf recompute)
        (ay_ecsg2_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ecsg2_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ecsg2_DiagnosticSubstitutionGuard
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_ecsg2_PublicResult originalCnf model certificate conflict exitCode ->
    ay_ecsg2_Conj
      (ay_ecsg2_NoSemanticClaim diagnostic)
      (ay_ecsg2_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_ecsg2_conj_intro
    (ay_ecsg2_NoSemanticClaim diagnostic)
    (ay_ecsg2_RecomputeObligation currentCnf recompute)
    (ay_ecsg2_diagnostic_no_claim
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic
      diagnosticGuard)
    (ay_ecsg2_diagnostic_recompute
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic
      diagnosticGuard)

theorem ay_ecsg2_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_ecsg2_DiagnosticSubstitutionGuard
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_ecsg2_ExitCodeSound exitCode (ay_ecsg2_Sat originalCnf model) ->
    ay_ecsg2_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_ecsg2_diagnostic_no_claim
    currentCnf classMismatch representativeMismatch substitutionMismatch
    rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
    buildMismatch validatorMismatch auditMismatch recompute diagnostic
    diagnosticGuard

theorem ay_ecsg2_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (classMismatch representativeMismatch substitutionMismatch rewriteMismatch : Prop)
    (equivalenceMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_ecsg2_DiagnosticSubstitutionGuard
      currentCnf classMismatch representativeMismatch substitutionMismatch
      rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
      buildMismatch validatorMismatch auditMismatch recompute diagnostic ->
    ay_ecsg2_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ecsg2_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_ecsg2_diagnostic_no_claim
    currentCnf classMismatch representativeMismatch substitutionMismatch
    rewriteMismatch equivalenceMismatch modelMismatch replayMismatch
    buildMismatch validatorMismatch auditMismatch recompute diagnostic
    diagnosticGuard
