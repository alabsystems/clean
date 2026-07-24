-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Watched-literal rewrite replay soundness for preprocessing. The
-- propositions stand for replayable clause coverage, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_pwlr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pwlr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pwlr_Equisat (before : Prop) (after : Prop) :=
  ay_pwlr_Conj (before -> after) (after -> before)

def ay_pwlr_Sat (cnf : Prop) (model : Prop) :=
  ay_pwlr_Conj cnf model

def ay_pwlr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pwlr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pwlr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pwlr_ClauseCoverage
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop) :=
  ay_pwlr_Conj coverageWitness
    (rewrittenClauses -> coveredClauses)

def ay_pwlr_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_pwlr_Conj representativeWitness
    (ay_pwlr_IdMatch oldRepresentative newRepresentative)

def ay_pwlr_ModelReconstruction
    (rewrittenCnf : Prop) (originalCnf : Prop)
    (rewrittenModel : Prop) (originalModel : Prop) :=
  ay_pwlr_Sat rewrittenCnf rewrittenModel ->
    ay_pwlr_Sat originalCnf originalModel

def ay_pwlr_ProofReconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pwlr_Replay rewrittenCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pwlr_DigestMembership
    (rewriteDigest : Prop) (manifestDigest : Prop) :=
  ay_pwlr_Conj rewriteDigest manifestDigest

def ay_pwlr_CheckerReplay
    (rewriteCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pwlr_Conj rewriteCertificate checkerAccepted

def ay_pwlr_FingerprintAgreement
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pwlr_Conj fingerprintWitness
    (ay_pwlr_IdMatch originalFingerprint rewrittenFingerprint)

def ay_pwlr_AcceptedRewriteReplay
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pwlr_Conj
    (ay_pwlr_ClauseCoverage
      rewrittenClauses coveredClauses coverageWitness)
    (ay_pwlr_Conj
      (ay_pwlr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pwlr_Conj
        (ay_pwlr_Equisat originalCnf rewrittenCnf)
        (ay_pwlr_Conj
          (ay_pwlr_ModelReconstruction
            rewrittenCnf originalCnf rewrittenModel originalModel)
          (ay_pwlr_Conj
            (ay_pwlr_ProofReconstruction
              originalCnf rewrittenCnf certificate conflict)
            (ay_pwlr_Conj
              (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
              (ay_pwlr_Conj
                (ay_pwlr_CheckerReplay
                  rewriteCertificate checkerAccepted)
                (ay_pwlr_FingerprintAgreement
                  originalFingerprint rewrittenFingerprint
                  fingerprintWitness)))))))

def ay_pwlr_AcceptedRewriteLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pwlr_Conj previousLog
    (ay_pwlr_Conj
      (ay_pwlr_AcceptedRewriteReplay
        originalCnf rewrittenCnf rewrittenClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative
        representativeWitness rewrittenModel originalModel certificate conflict
        rewriteDigest manifestDigest rewriteCertificate checkerAccepted
        originalFingerprint rewrittenFingerprint fingerprintWitness)
      nextLog)

def ay_pwlr_RewriteFailure
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :=
  ay_pwlr_Disj rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))

def ay_pwlr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pwlr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pwlr_Conj currentCnf recompute

def ay_pwlr_DiagnosticRewriteLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pwlr_Conj previousLog
    (ay_pwlr_Conj
      (ay_pwlr_Conj
        (ay_pwlr_RewriteFailure
          rewriteMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedRewrite)
        (ay_pwlr_Conj
          (ay_pwlr_RecomputeObligation currentCnf recompute)
          (ay_pwlr_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pwlr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pwlr_Conj exitCode claim

def ay_pwlr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pwlr_Disj
    (ay_pwlr_ExitCodeSound exitCode (ay_pwlr_Sat originalCnf model))
    (ay_pwlr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pwlr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pwlr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pwlr_conj_left
    (left : Prop) (right : Prop) :
    ay_pwlr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pwlr_conj_right
    (left : Prop) (right : Prop) :
    ay_pwlr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pwlr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pwlr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pwlr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pwlr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pwlr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pwlr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pwlr_conj_left (before -> after) (after -> before) eq

theorem ay_pwlr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pwlr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pwlr_conj_right (before -> after) (after -> before) eq

theorem ay_pwlr_rewrite_clause_coverage
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_ClauseCoverage rewrittenClauses coveredClauses coverageWitness := by
  intro accepted
  exact ay_pwlr_conj_left
    (ay_pwlr_ClauseCoverage rewrittenClauses coveredClauses coverageWitness)
    (ay_pwlr_Conj
      (ay_pwlr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pwlr_Conj
        (ay_pwlr_Equisat originalCnf rewrittenCnf)
        (ay_pwlr_Conj
          (ay_pwlr_ModelReconstruction
            rewrittenCnf originalCnf rewrittenModel originalModel)
          (ay_pwlr_Conj
            (ay_pwlr_ProofReconstruction
              originalCnf rewrittenCnf certificate conflict)
            (ay_pwlr_Conj
              (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
              (ay_pwlr_Conj
                (ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted)
                (ay_pwlr_FingerprintAgreement
                  originalFingerprint rewrittenFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_pwlr_rewrite_representative
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_pwlr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_pwlr_rewrite_equisat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_Equisat originalCnf rewrittenCnf := by
  intro accepted
  exact accepted
    (ay_pwlr_Equisat originalCnf rewrittenCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_Equisat originalCnf rewrittenCnf)
        (fun _rep rest2 =>
          rest2
            (ay_pwlr_Equisat originalCnf rewrittenCnf)
            (fun eq _tail => eq)))

theorem ay_pwlr_rewrite_model_reconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_ModelReconstruction rewrittenCnf originalCnf rewrittenModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pwlr_ModelReconstruction
      rewrittenCnf originalCnf rewrittenModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_ModelReconstruction
          rewrittenCnf originalCnf rewrittenModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_pwlr_ModelReconstruction
              rewrittenCnf originalCnf rewrittenModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_pwlr_ModelReconstruction
                  rewrittenCnf originalCnf rewrittenModel originalModel)
                (fun model _tail => model))))

theorem ay_pwlr_rewrite_proof_reconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_ProofReconstruction originalCnf rewrittenCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pwlr_ProofReconstruction originalCnf rewrittenCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_ProofReconstruction originalCnf rewrittenCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_pwlr_ProofReconstruction
              originalCnf rewrittenCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pwlr_ProofReconstruction
                  originalCnf rewrittenCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pwlr_ProofReconstruction
                      originalCnf rewrittenCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pwlr_rewrite_digest
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_DigestMembership rewriteDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pwlr_DigestMembership rewriteDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_pwlr_rewrite_checker
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pwlr_CheckerReplay rewriteCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pwlr_CheckerReplay
                          rewriteCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pwlr_CheckerReplay
                              rewriteCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_pwlr_rewrite_fingerprint
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_FingerprintAgreement
      originalFingerprint rewrittenFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pwlr_FingerprintAgreement
      originalFingerprint rewrittenFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pwlr_FingerprintAgreement
          originalFingerprint rewrittenFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pwlr_FingerprintAgreement
              originalFingerprint rewrittenFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pwlr_FingerprintAgreement
                  originalFingerprint rewrittenFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pwlr_FingerprintAgreement
                      originalFingerprint rewrittenFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pwlr_FingerprintAgreement
                          originalFingerprint rewrittenFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pwlr_FingerprintAgreement
                              originalFingerprint rewrittenFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_pwlr_sat_pullback
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_Sat rewrittenCnf rewrittenModel ->
    ay_pwlr_Sat originalCnf originalModel := by
  intro accepted rewrittenSat
  exact
    (ay_pwlr_rewrite_model_reconstruction
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      rewrittenModel originalModel certificate conflict rewriteDigest
      manifestDigest rewriteCertificate checkerAccepted originalFingerprint
      rewrittenFingerprint fingerprintWitness accepted)
      rewrittenSat

theorem ay_pwlr_unsat_pushback
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_Replay rewrittenCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pwlr_rewrite_proof_reconstruction
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      rewrittenModel originalModel certificate conflict rewriteDigest
      manifestDigest rewriteCertificate checkerAccepted originalFingerprint
      rewrittenFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pwlr_public_sat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_Sat rewrittenCnf rewrittenModel ->
    exitCode ->
    ay_pwlr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted rewrittenSat exit
  exact ay_pwlr_disj_left
    (ay_pwlr_ExitCodeSound exitCode (ay_pwlr_Sat originalCnf originalModel))
    (ay_pwlr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pwlr_conj_intro exitCode
      (ay_pwlr_Sat originalCnf originalModel)
      exit
      (ay_pwlr_sat_pullback
        originalCnf rewrittenCnf rewrittenClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative representativeWitness
        rewrittenModel originalModel certificate conflict rewriteDigest
        manifestDigest rewriteCertificate checkerAccepted originalFingerprint
        rewrittenFingerprint fingerprintWitness accepted rewrittenSat))

theorem ay_pwlr_public_unsat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (rewrittenClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (rewriteDigest : Prop) (manifestDigest : Prop)
    (rewriteCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pwlr_AcceptedRewriteReplay
      originalCnf rewrittenCnf rewrittenClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness rewrittenModel originalModel certificate conflict
      rewriteDigest manifestDigest rewriteCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness ->
    ay_pwlr_Replay rewrittenCnf certificate conflict ->
    exitCode ->
    ay_pwlr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pwlr_disj_right
    (ay_pwlr_ExitCodeSound exitCode (ay_pwlr_Sat originalCnf originalModel))
    (ay_pwlr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pwlr_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pwlr_unsat_pushback
          originalCnf rewrittenCnf rewrittenClauses coveredClauses
          coverageWitness oldRepresentative newRepresentative
          representativeWitness rewrittenModel originalModel certificate conflict
          rewriteDigest manifestDigest rewriteCertificate checkerAccepted
          originalFingerprint rewrittenFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_pwlr_failure_rewrite_mismatch
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    rewriteMismatch ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro mismatch
  exact ay_pwlr_disj_left rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    mismatch

theorem ay_pwlr_failure_missing_coverage
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    missingCoverage ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro missing
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_left missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      missing)

theorem ay_pwlr_failure_representative_mismatch
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    representativeMismatch ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro mismatch
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_right missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      (ay_pwlr_disj_left representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))
        mismatch))

theorem ay_pwlr_failure_broken_reconstruction
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    brokenReconstruction ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro broken
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_right missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      (ay_pwlr_disj_right representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))
        (ay_pwlr_disj_left brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))
          broken)))

theorem ay_pwlr_failure_digest_mismatch
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    digestMismatch ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro mismatch
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_right missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      (ay_pwlr_disj_right representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))
        (ay_pwlr_disj_right brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))
          (ay_pwlr_disj_left digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))
            mismatch))))

theorem ay_pwlr_failure_replay_rejected
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    replayRejected ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro rejected
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_right missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      (ay_pwlr_disj_right representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))
        (ay_pwlr_disj_right brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))
          (ay_pwlr_disj_right digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))
            (ay_pwlr_disj_left replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)
              rejected)))))

theorem ay_pwlr_failure_fingerprint_drift
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    fingerprintDrift ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro drift
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_right missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      (ay_pwlr_disj_right representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))
        (ay_pwlr_disj_right brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))
          (ay_pwlr_disj_right digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))
            (ay_pwlr_disj_right replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)
              (ay_pwlr_disj_left fingerprintDrift uncheckedRewrite drift))))))

theorem ay_pwlr_failure_unchecked_rewrite
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop) :
    uncheckedRewrite ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro unchecked
  exact ay_pwlr_disj_right rewriteMismatch
    (ay_pwlr_Disj missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))))
    (ay_pwlr_disj_right missingCoverage
      (ay_pwlr_Disj representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))))
      (ay_pwlr_disj_right representativeMismatch
        (ay_pwlr_Disj brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))))
        (ay_pwlr_disj_right brokenReconstruction
          (ay_pwlr_Disj digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)))
          (ay_pwlr_disj_right digestMismatch
            (ay_pwlr_Disj replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite))
            (ay_pwlr_disj_right replayRejected
              (ay_pwlr_Disj fingerprintDrift uncheckedRewrite)
              (ay_pwlr_disj_right fingerprintDrift uncheckedRewrite
                unchecked))))))

theorem ay_pwlr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pwlr_DiagnosticRewriteLogEntry
      previousLog nextLog currentCnf rewriteMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedRewrite recompute diagnostic ->
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite := by
  intro entry
  exact entry
    (ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite)
    (fun _previous rest1 =>
      rest1
        (ay_pwlr_RewriteFailure
          rewriteMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedRewrite)
        (fun body _next =>
          body
            (ay_pwlr_RewriteFailure
              rewriteMismatch missingCoverage representativeMismatch
              brokenReconstruction digestMismatch replayRejected fingerprintDrift
              uncheckedRewrite)
            (fun failure _tail => failure)))

theorem ay_pwlr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pwlr_DiagnosticRewriteLogEntry
      previousLog nextLog currentCnf rewriteMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedRewrite recompute diagnostic ->
    ay_pwlr_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pwlr_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pwlr_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pwlr_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pwlr_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pwlr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pwlr_DiagnosticRewriteLogEntry
      previousLog nextLog currentCnf rewriteMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedRewrite recompute diagnostic ->
    ay_pwlr_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pwlr_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pwlr_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pwlr_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pwlr_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pwlr_unchecked_no_public_blessing
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop)
    (diagnostic : Prop) :
    uncheckedRewrite ->
    diagnostic ->
    ay_pwlr_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_pwlr_failure_no_claim
    (rewriteMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedRewrite : Prop)
    (diagnostic : Prop) :
    ay_pwlr_RewriteFailure
      rewriteMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedRewrite ->
    diagnostic ->
    ay_pwlr_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
