-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-subsuming-resolution preprocessing guard soundness.
-- The propositions stand for original formula fingerprints, candidate clause
-- ledgers, pivot literal witnesses, partner clause digests, resolvent/
-- subsumption witnesses, strengthened-clause digests, deletion/strengthening
-- ledgers, model preservation, UNSAT replay/equisat evidence, build/validator
-- gates, fallback no-claim paths, audit transcripts, and public reports.

def ay_ssrg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ssrg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ssrg_Equisat (original : Prop) (strengthened : Prop) :=
  ay_ssrg_Conj (original -> strengthened) (strengthened -> original)

def ay_ssrg_Sat (cnf : Prop) (model : Prop) :=
  ay_ssrg_Conj cnf model

def ay_ssrg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_ssrg_OriginalFormulaFingerprint
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop) :=
  ay_ssrg_Conj fingerprintManifest (fingerprint -> fingerprintAccepted)

def ay_ssrg_CandidateClauseLedger
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :=
  ay_ssrg_Conj candidateCoverage
    (candidateClauseLedger -> candidateAccepted)

def ay_ssrg_PivotLiteralWitness
    (pivotLiteralWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop) :=
  ay_ssrg_Conj pivotCoverage (pivotLiteralWitness -> pivotAccepted)

def ay_ssrg_PartnerClauseDigest
    (partnerClauseDigest : Prop) (partnerDigestAccepted : Prop)
    (partnerDigestManifest : Prop) :=
  ay_ssrg_Conj partnerDigestManifest
    (partnerClauseDigest -> partnerDigestAccepted)

def ay_ssrg_ResolventSubsumptionWitness
    (resolventSubsumptionWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :=
  ay_ssrg_Conj resolventCoverage
    (resolventSubsumptionWitness -> resolventAccepted)

def ay_ssrg_StrengthenedClauseDigest
    (strengthenedClauseDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedDigestManifest : Prop) :=
  ay_ssrg_Conj strengthenedDigestManifest
    (strengthenedClauseDigest -> strengthenedDigestAccepted)

def ay_ssrg_DeletionStrengtheningLedger
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop) :=
  ay_ssrg_Conj ledgerCoverage
    (deletionStrengtheningLedger -> ledgerAccepted)

def ay_ssrg_ValidatorGate
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop) :=
  ay_ssrg_Conj checkerAccepted
    (ay_ssrg_Conj validatorAccepted validatorVersion)

def ay_ssrg_ModelPreservationWitness
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop) :=
  ay_ssrg_Sat strengthenedCnf strengthenedModel ->
    ay_ssrg_Sat originalCnf originalModel

def ay_ssrg_UnsatReplayEquisatWitness
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ssrg_Replay strengthenedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_ssrg_ReconstructionEvidence
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_ssrg_Conj
    (ay_ssrg_ModelPreservationWitness
      strengthenedCnf originalCnf strengthenedModel originalModel)
    (ay_ssrg_UnsatReplayEquisatWitness
      originalCnf strengthenedCnf certificate conflict)

def ay_ssrg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_ssrg_Conj binaryFingerprint buildReproducible

def ay_ssrg_FallbackNoClaimPath
    (baselineAvailable : Prop) (noClaimPath : Prop) :=
  ay_ssrg_Conj baselineAvailable noClaimPath

def ay_ssrg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_ssrg_Conj auditAppended auditAppendOnly

def ay_ssrg_AcceptedSelfSubsumingResolutionGuard
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (pivotLiteralWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (partnerClauseDigest : Prop) (partnerDigestAccepted : Prop)
    (partnerDigestManifest : Prop)
    (resolventSubsumptionWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (strengthenedClauseDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedDigestManifest : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_ssrg_OriginalFormulaFingerprint
       fingerprint fingerprintAccepted fingerprintManifest ->
     ay_ssrg_CandidateClauseLedger
       candidateClauseLedger candidateAccepted candidateCoverage ->
     ay_ssrg_PivotLiteralWitness pivotLiteralWitness pivotAccepted pivotCoverage ->
     ay_ssrg_PartnerClauseDigest
       partnerClauseDigest partnerDigestAccepted partnerDigestManifest ->
     ay_ssrg_ResolventSubsumptionWitness
       resolventSubsumptionWitness resolventAccepted resolventCoverage ->
     ay_ssrg_StrengthenedClauseDigest
       strengthenedClauseDigest strengthenedDigestAccepted strengthenedDigestManifest ->
     ay_ssrg_DeletionStrengtheningLedger
       deletionStrengtheningLedger ledgerAccepted ledgerCoverage ->
     ay_ssrg_ReconstructionEvidence
       strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict ->
     ay_ssrg_Equisat originalCnf strengthenedCnf ->
     ay_ssrg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_ssrg_ValidatorGate checkerAccepted validatorAccepted validatorVersion ->
     ay_ssrg_FallbackNoClaimPath baselineAvailable noClaimPath ->
     ay_ssrg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_ssrg_SsrGuardFailure
    (candidateMismatch : Prop) (pivotMismatch : Prop)
    (partnerMismatch : Prop) (resolventMismatch : Prop)
    (strengtheningMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (candidateMismatch -> result) ->
    (pivotMismatch -> result) ->
    (partnerMismatch -> result) ->
    (resolventMismatch -> result) ->
    (strengtheningMismatch -> result) ->
    (modelMismatch -> result) ->
    (replayMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ssrg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_ssrg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_ssrg_Conj currentCnf recompute

def ay_ssrg_DiagnosticSsrGuard
    (currentCnf : Prop)
    (candidateMismatch : Prop) (pivotMismatch : Prop)
    (partnerMismatch : Prop) (resolventMismatch : Prop)
    (strengtheningMismatch : Prop) (modelMismatch : Prop)
    (replayMismatch : Prop) (buildMismatch : Prop)
    (validatorMismatch : Prop) (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_ssrg_Conj
    (ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch)
    (ay_ssrg_Conj
      (ay_ssrg_RecomputeObligation currentCnf recompute)
      (ay_ssrg_NoSemanticClaim diagnostic))

def ay_ssrg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_ssrg_Conj exitCode claim

def ay_ssrg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_ssrg_Disj
    (ay_ssrg_ExitCodeSound exitCode (ay_ssrg_Sat originalCnf model))
    (ay_ssrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_ssrg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_ssrg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_ssrg_conj_left
    (left : Prop) (right : Prop) :
    ay_ssrg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_ssrg_conj_right
    (left : Prop) (right : Prop) :
    ay_ssrg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_ssrg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_ssrg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_ssrg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_ssrg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_ssrg_equisat_forward
    (original : Prop) (strengthened : Prop) :
    ay_ssrg_Equisat original strengthened -> original -> strengthened := by
  intro eqsat
  exact ay_ssrg_conj_left (original -> strengthened) (strengthened -> original) eqsat

theorem ay_ssrg_equisat_backward
    (original : Prop) (strengthened : Prop) :
    ay_ssrg_Equisat original strengthened -> strengthened -> original := by
  intro eqsat
  exact ay_ssrg_conj_right (original -> strengthened) (strengthened -> original) eqsat

theorem ay_ssrg_candidate_clause_ledger_applies
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop) :
    ay_ssrg_CandidateClauseLedger
      candidateClauseLedger candidateAccepted candidateCoverage ->
    candidateClauseLedger -> candidateAccepted := by
  intro ledger
  exact ay_ssrg_conj_right
    candidateCoverage (candidateClauseLedger -> candidateAccepted) ledger

theorem ay_ssrg_pivot_literal_witness_applies
    (pivotLiteralWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop) :
    ay_ssrg_PivotLiteralWitness
      pivotLiteralWitness pivotAccepted pivotCoverage ->
    pivotLiteralWitness -> pivotAccepted := by
  intro witness
  exact ay_ssrg_conj_right
    pivotCoverage (pivotLiteralWitness -> pivotAccepted) witness

theorem ay_ssrg_partner_clause_digest_applies
    (partnerClauseDigest : Prop) (partnerDigestAccepted : Prop)
    (partnerDigestManifest : Prop) :
    ay_ssrg_PartnerClauseDigest
      partnerClauseDigest partnerDigestAccepted partnerDigestManifest ->
    partnerClauseDigest -> partnerDigestAccepted := by
  intro digest
  exact ay_ssrg_conj_right
    partnerDigestManifest (partnerClauseDigest -> partnerDigestAccepted) digest

theorem ay_ssrg_resolvent_subsumption_witness_applies
    (resolventSubsumptionWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :
    ay_ssrg_ResolventSubsumptionWitness
      resolventSubsumptionWitness resolventAccepted resolventCoverage ->
    resolventSubsumptionWitness -> resolventAccepted := by
  intro witness
  exact ay_ssrg_conj_right
    resolventCoverage (resolventSubsumptionWitness -> resolventAccepted)
    witness

theorem ay_ssrg_strengthened_clause_digest_applies
    (strengthenedClauseDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedDigestManifest : Prop) :
    ay_ssrg_StrengthenedClauseDigest
      strengthenedClauseDigest strengthenedDigestAccepted strengthenedDigestManifest ->
    strengthenedClauseDigest -> strengthenedDigestAccepted := by
  intro digest
  exact ay_ssrg_conj_right
    strengthenedDigestManifest
    (strengthenedClauseDigest -> strengthenedDigestAccepted)
    digest

theorem ay_ssrg_model_preservation
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ReconstructionEvidence
      strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict ->
    ay_ssrg_Sat strengthenedCnf strengthenedModel ->
    ay_ssrg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_ssrg_conj_left
    (ay_ssrg_ModelPreservationWitness
      strengthenedCnf originalCnf strengthenedModel originalModel)
    (ay_ssrg_UnsatReplayEquisatWitness
      originalCnf strengthenedCnf certificate conflict)
    witnesses

theorem ay_ssrg_unsat_replay
    (strengthenedCnf : Prop) (originalCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ReconstructionEvidence
      strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict ->
    ay_ssrg_Replay strengthenedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_ssrg_conj_right
    (ay_ssrg_ModelPreservationWitness
      strengthenedCnf originalCnf strengthenedModel originalModel)
    (ay_ssrg_UnsatReplayEquisatWitness
      originalCnf strengthenedCnf certificate conflict)
    witnesses

theorem ay_ssrg_accepted_equisat
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (pivotLiteralWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (partnerClauseDigest : Prop) (partnerDigestAccepted : Prop)
    (partnerDigestManifest : Prop)
    (resolventSubsumptionWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (strengthenedClauseDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedDigestManifest : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionGuard
      originalCnf strengthenedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      candidateClauseLedger candidateAccepted candidateCoverage
      pivotLiteralWitness pivotAccepted pivotCoverage
      partnerClauseDigest partnerDigestAccepted partnerDigestManifest
      resolventSubsumptionWitness resolventAccepted resolventCoverage
      strengthenedClauseDigest strengthenedDigestAccepted strengthenedDigestManifest
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerAccepted validatorAccepted validatorVersion
      strengthenedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_ssrg_Equisat originalCnf strengthenedCnf := by
  intro accepted
  exact accepted (ay_ssrg_Equisat originalCnf strengthenedCnf)
    (fun _fingerprint _candidate _pivot _partner _resolvent _strengthened
      _ledger _reconstruct eqsat _build _validator _fallback _audit => eqsat)

theorem ay_ssrg_accepted_reconstruction
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (fingerprint : Prop) (fingerprintAccepted : Prop)
    (fingerprintManifest : Prop)
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (pivotLiteralWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (partnerClauseDigest : Prop) (partnerDigestAccepted : Prop)
    (partnerDigestManifest : Prop)
    (resolventSubsumptionWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop)
    (strengthenedClauseDigest : Prop) (strengthenedDigestAccepted : Prop)
    (strengthenedDigestManifest : Prop)
    (deletionStrengtheningLedger : Prop) (ledgerAccepted : Prop)
    (ledgerCoverage : Prop)
    (checkerAccepted : Prop) (validatorAccepted : Prop)
    (validatorVersion : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (baselineAvailable : Prop) (noClaimPath : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_ssrg_AcceptedSelfSubsumingResolutionGuard
      originalCnf strengthenedCnf
      fingerprint fingerprintAccepted fingerprintManifest
      candidateClauseLedger candidateAccepted candidateCoverage
      pivotLiteralWitness pivotAccepted pivotCoverage
      partnerClauseDigest partnerDigestAccepted partnerDigestManifest
      resolventSubsumptionWitness resolventAccepted resolventCoverage
      strengthenedClauseDigest strengthenedDigestAccepted strengthenedDigestManifest
      deletionStrengtheningLedger ledgerAccepted ledgerCoverage
      checkerAccepted validatorAccepted validatorVersion
      strengthenedModel originalModel certificate conflict
      binaryFingerprint buildReproducible
      baselineAvailable noClaimPath auditAppended auditAppendOnly ->
    ay_ssrg_ReconstructionEvidence
      strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_ssrg_ReconstructionEvidence
      strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict)
    (fun _fingerprint _candidate _pivot _partner _resolvent _strengthened
      _ledger reconstruct _eqsat _build _validator _fallback _audit =>
      reconstruct)

theorem ay_ssrg_strengthening_has_exact_evidence
    (candidateClauseLedger : Prop) (candidateAccepted : Prop)
    (candidateCoverage : Prop)
    (pivotLiteralWitness : Prop) (pivotAccepted : Prop)
    (pivotCoverage : Prop)
    (partnerClauseDigest : Prop) (partnerDigestAccepted : Prop)
    (partnerDigestManifest : Prop)
    (resolventSubsumptionWitness : Prop) (resolventAccepted : Prop)
    (resolventCoverage : Prop) :
    ay_ssrg_CandidateClauseLedger
      candidateClauseLedger candidateAccepted candidateCoverage ->
    ay_ssrg_PivotLiteralWitness pivotLiteralWitness pivotAccepted pivotCoverage ->
    ay_ssrg_PartnerClauseDigest
      partnerClauseDigest partnerDigestAccepted partnerDigestManifest ->
    ay_ssrg_ResolventSubsumptionWitness
      resolventSubsumptionWitness resolventAccepted resolventCoverage ->
    candidateClauseLedger -> pivotLiteralWitness -> partnerClauseDigest ->
    resolventSubsumptionWitness ->
    ay_ssrg_Conj candidateAccepted
      (ay_ssrg_Conj pivotAccepted
        (ay_ssrg_Conj partnerDigestAccepted resolventAccepted)) := by
  intro candidateOk pivotOk partnerOk resolventOk candidate pivot partner resolvent
  exact ay_ssrg_conj_intro candidateAccepted
    (ay_ssrg_Conj pivotAccepted
      (ay_ssrg_Conj partnerDigestAccepted resolventAccepted))
    (ay_ssrg_candidate_clause_ledger_applies
      candidateClauseLedger candidateAccepted candidateCoverage candidateOk candidate)
    (ay_ssrg_conj_intro pivotAccepted
      (ay_ssrg_Conj partnerDigestAccepted resolventAccepted)
      (ay_ssrg_pivot_literal_witness_applies
        pivotLiteralWitness pivotAccepted pivotCoverage pivotOk pivot)
      (ay_ssrg_conj_intro partnerDigestAccepted resolventAccepted
        (ay_ssrg_partner_clause_digest_applies
          partnerClauseDigest partnerDigestAccepted partnerDigestManifest
          partnerOk partner)
        (ay_ssrg_resolvent_subsumption_witness_applies
          resolventSubsumptionWitness resolventAccepted resolventCoverage
          resolventOk resolvent)))

theorem ay_ssrg_sat_pullback
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ReconstructionEvidence
      strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict ->
    ay_ssrg_Sat strengthenedCnf strengthenedModel ->
    ay_ssrg_Sat originalCnf originalModel := by
  intro witnesses satStrengthened
  exact ay_ssrg_model_preservation
    strengthenedCnf originalCnf strengthenedModel originalModel
    certificate conflict witnesses satStrengthened

theorem ay_ssrg_unsat_pushback
    (originalCnf : Prop) (strengthenedCnf : Prop)
    (strengthenedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_ssrg_ReconstructionEvidence
      strengthenedCnf originalCnf strengthenedModel originalModel certificate conflict ->
    ay_ssrg_Replay strengthenedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_ssrg_unsat_replay
    strengthenedCnf originalCnf strengthenedModel originalModel
    certificate conflict witnesses replay

theorem ay_ssrg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ssrg_ExitCodeSound exitCode (ay_ssrg_Sat originalCnf originalModel) ->
    ay_ssrg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_ssrg_disj_left
    (ay_ssrg_ExitCodeSound exitCode (ay_ssrg_Sat originalCnf originalModel))
    (ay_ssrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_ssrg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ssrg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ssrg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_ssrg_disj_right
    (ay_ssrg_ExitCodeSound exitCode (ay_ssrg_Sat originalCnf originalModel))
    (ay_ssrg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_ssrg_failure_candidate
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    candidateMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result candidate_case _pivot_case _partner_case _resolvent_case
    _strength_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact candidate_case h

theorem ay_ssrg_failure_pivot
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    pivotMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case pivot_case _partner_case _resolvent_case
    _strength_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact pivot_case h

theorem ay_ssrg_failure_partner
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    partnerMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case partner_case _resolvent_case
    _strength_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact partner_case h

theorem ay_ssrg_failure_resolvent
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    resolventMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case resolvent_case
    _strength_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact resolvent_case h

theorem ay_ssrg_failure_strengthening
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    strengtheningMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case _resolvent_case
    strength_case _model_case _replay_case _build_case _validator_case
    _audit_case
  exact strength_case h

theorem ay_ssrg_failure_model
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    modelMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case _resolvent_case
    _strength_case model_case _replay_case _build_case _validator_case
    _audit_case
  exact model_case h

theorem ay_ssrg_failure_replay
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    replayMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case _resolvent_case
    _strength_case _model_case replay_case _build_case _validator_case
    _audit_case
  exact replay_case h

theorem ay_ssrg_failure_build
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    buildMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case _resolvent_case
    _strength_case _model_case _replay_case build_case _validator_case
    _audit_case
  exact build_case h

theorem ay_ssrg_failure_validator
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    validatorMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case _resolvent_case
    _strength_case _model_case _replay_case _build_case validator_case
    _audit_case
  exact validator_case h

theorem ay_ssrg_failure_audit
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop) :
    auditMismatch ->
    ay_ssrg_SsrGuardFailure
      candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch := by
  intro h result _candidate_case _pivot_case _partner_case _resolvent_case
    _strength_case _model_case _replay_case _build_case _validator_case
    audit_case
  exact audit_case h

theorem ay_ssrg_diagnostic_no_claim
    (currentCnf : Prop)
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ssrg_DiagnosticSsrGuard
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ssrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_ssrg_conj_right
    (ay_ssrg_RecomputeObligation currentCnf recompute)
    (ay_ssrg_NoSemanticClaim diagnostic)
    (ay_ssrg_conj_right
      (ay_ssrg_SsrGuardFailure
        candidateMismatch pivotMismatch partnerMismatch resolventMismatch
        strengtheningMismatch modelMismatch replayMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_ssrg_Conj
        (ay_ssrg_RecomputeObligation currentCnf recompute)
        (ay_ssrg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ssrg_diagnostic_recompute
    (currentCnf : Prop)
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_ssrg_DiagnosticSsrGuard
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ssrg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_ssrg_conj_left
    (ay_ssrg_RecomputeObligation currentCnf recompute)
    (ay_ssrg_NoSemanticClaim diagnostic)
    (ay_ssrg_conj_right
      (ay_ssrg_SsrGuardFailure
        candidateMismatch pivotMismatch partnerMismatch resolventMismatch
        strengtheningMismatch modelMismatch replayMismatch buildMismatch
        validatorMismatch auditMismatch)
      (ay_ssrg_Conj
        (ay_ssrg_RecomputeObligation currentCnf recompute)
        (ay_ssrg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_ssrg_failed_guard_cannot_bless_public_result
    (currentCnf : Prop)
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_ssrg_DiagnosticSsrGuard
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ssrg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_ssrg_Conj
      (ay_ssrg_NoSemanticClaim diagnostic)
      (ay_ssrg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_ssrg_conj_intro
    (ay_ssrg_NoSemanticClaim diagnostic)
    (ay_ssrg_RecomputeObligation currentCnf recompute)
    (ay_ssrg_diagnostic_no_claim
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)
    (ay_ssrg_diagnostic_recompute
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_ssrg_failed_guard_cannot_bless_public_sat
    (currentCnf : Prop)
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_ssrg_DiagnosticSsrGuard
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ssrg_ExitCodeSound exitCode (ay_ssrg_Sat originalCnf model) ->
    ay_ssrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_ssrg_diagnostic_no_claim
    currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
    strengtheningMismatch modelMismatch replayMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard

theorem ay_ssrg_failed_guard_cannot_bless_public_unsat
    (currentCnf : Prop)
    (candidateMismatch pivotMismatch partnerMismatch resolventMismatch : Prop)
    (strengtheningMismatch modelMismatch replayMismatch buildMismatch : Prop)
    (validatorMismatch auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_ssrg_DiagnosticSsrGuard
      currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
      strengtheningMismatch modelMismatch replayMismatch buildMismatch
      validatorMismatch auditMismatch recompute diagnostic ->
    ay_ssrg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_ssrg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_ssrg_diagnostic_no_claim
    currentCnf candidateMismatch pivotMismatch partnerMismatch resolventMismatch
    strengtheningMismatch modelMismatch replayMismatch buildMismatch
    validatorMismatch auditMismatch recompute diagnostic diagnosticGuard
