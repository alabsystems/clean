-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Equivalence-hash congruence soundness for preprocessing. The propositions
-- stand for equivalence-class lineage, hash collision checks, representative
-- maps, model/proof reconstruction hooks, digest membership, checker replay,
-- original-instance fingerprint agreement, diagnostics, and public SAT/UNSAT
-- reports.

def ay_pehc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pehc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pehc_Equisat (before : Prop) (after : Prop) :=
  ay_pehc_Conj (before -> after) (after -> before)

def ay_pehc_Sat (cnf : Prop) (model : Prop) :=
  ay_pehc_Conj cnf model

def ay_pehc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pehc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pehc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pehc_EquivalenceLineage
    (sourceClasses : Prop) (mergedClasses : Prop) (lineageWitness : Prop) :=
  ay_pehc_Conj lineageWitness
    (ay_pehc_IdMatch sourceClasses mergedClasses)

def ay_pehc_HashCollisionCheck
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop) :=
  ay_pehc_Conj hashWitness
    (ay_pehc_Conj hashBucket collisionRejected)

def ay_pehc_RepresentativeMap
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop) :=
  ay_pehc_Conj representativeWitness
    (mergedLiteral -> representativeLiteral)

def ay_pehc_ModelReconstruction
    (hashedCnf : Prop) (originalCnf : Prop)
    (hashedModel : Prop) (originalModel : Prop) :=
  ay_pehc_Sat hashedCnf hashedModel ->
    ay_pehc_Sat originalCnf originalModel

def ay_pehc_ProofReconstruction
    (originalCnf : Prop) (hashedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pehc_Replay hashedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pehc_DigestMembership
    (hashDigest : Prop) (manifestDigest : Prop) :=
  ay_pehc_Conj hashDigest manifestDigest

def ay_pehc_CheckerReplay
    (hashCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pehc_Conj hashCertificate checkerAccepted

def ay_pehc_FingerprintAgreement
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pehc_Conj fingerprintWitness
    (ay_pehc_IdMatch originalFingerprint hashedFingerprint)

def ay_pehc_AcceptedHashCongruence
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pehc_Conj
    (ay_pehc_EquivalenceLineage
      sourceClasses mergedClasses lineageWitness)
    (ay_pehc_Conj
      (ay_pehc_HashCollisionCheck
        hashBucket collisionRejected hashWitness)
      (ay_pehc_Conj
        (ay_pehc_RepresentativeMap
          mergedLiteral representativeLiteral representativeWitness)
        (ay_pehc_Conj
          (ay_pehc_Equisat originalCnf hashedCnf)
          (ay_pehc_Conj
            (ay_pehc_ModelReconstruction
              hashedCnf originalCnf hashedModel originalModel)
            (ay_pehc_Conj
              (ay_pehc_ProofReconstruction
                originalCnf hashedCnf certificate conflict)
              (ay_pehc_Conj
                (ay_pehc_DigestMembership hashDigest manifestDigest)
                (ay_pehc_Conj
                  (ay_pehc_CheckerReplay
                    hashCertificate checkerAccepted)
                  (ay_pehc_FingerprintAgreement
                    originalFingerprint hashedFingerprint
                    fingerprintWitness))))))))

def ay_pehc_AcceptedHashLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pehc_Conj previousLog
    (ay_pehc_Conj
      (ay_pehc_AcceptedHashCongruence
        originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
        hashBucket collisionRejected hashWitness mergedLiteral
        representativeLiteral representativeWitness hashedModel originalModel
        certificate conflict hashDigest manifestDigest hashCertificate
        checkerAccepted originalFingerprint hashedFingerprint
        fingerprintWitness)
      nextLog)

def ay_pehc_HashFailure
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :=
  ay_pehc_Disj hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))

def ay_pehc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pehc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pehc_Conj currentCnf recompute

def ay_pehc_DiagnosticHashLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pehc_Conj previousLog
    (ay_pehc_Conj
      (ay_pehc_Conj
        (ay_pehc_HashFailure
          hashCollision missingRepresentative brokenEquivalenceLineage
          staleReconstruction digestMismatch replayRejected fingerprintDrift)
        (ay_pehc_Conj
          (ay_pehc_RecomputeObligation currentCnf recompute)
          (ay_pehc_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pehc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pehc_Conj exitCode claim

def ay_pehc_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pehc_Disj
    (ay_pehc_ExitCodeSound exitCode (ay_pehc_Sat originalCnf model))
    (ay_pehc_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pehc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pehc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pehc_conj_left
    (left : Prop) (right : Prop) :
    ay_pehc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pehc_conj_right
    (left : Prop) (right : Prop) :
    ay_pehc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pehc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pehc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pehc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pehc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pehc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pehc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pehc_conj_left (before -> after) (after -> before) eq

theorem ay_pehc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pehc_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pehc_conj_right (before -> after) (after -> before) eq

theorem ay_pehc_hash_lineage
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_EquivalenceLineage
      sourceClasses mergedClasses lineageWitness := by
  intro accepted
  exact ay_pehc_conj_left
    (ay_pehc_EquivalenceLineage sourceClasses mergedClasses lineageWitness)
    (ay_pehc_Conj
      (ay_pehc_HashCollisionCheck
        hashBucket collisionRejected hashWitness)
      (ay_pehc_Conj
        (ay_pehc_RepresentativeMap
          mergedLiteral representativeLiteral representativeWitness)
        (ay_pehc_Conj
          (ay_pehc_Equisat originalCnf hashedCnf)
          (ay_pehc_Conj
            (ay_pehc_ModelReconstruction
              hashedCnf originalCnf hashedModel originalModel)
            (ay_pehc_Conj
              (ay_pehc_ProofReconstruction
                originalCnf hashedCnf certificate conflict)
              (ay_pehc_Conj
                (ay_pehc_DigestMembership hashDigest manifestDigest)
                (ay_pehc_Conj
                  (ay_pehc_CheckerReplay
                    hashCertificate checkerAccepted)
                  (ay_pehc_FingerprintAgreement
                    originalFingerprint hashedFingerprint
                    fingerprintWitness))))))))
    accepted

theorem ay_pehc_hash_collision_check
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_HashCollisionCheck hashBucket collisionRejected hashWitness := by
  intro accepted
  exact accepted
    (ay_pehc_HashCollisionCheck hashBucket collisionRejected hashWitness)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_HashCollisionCheck hashBucket collisionRejected hashWitness)
        (fun check _tail => check))

theorem ay_pehc_hash_representative
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_RepresentativeMap
      mergedLiteral representativeLiteral representativeWitness := by
  intro accepted
  exact accepted
    (ay_pehc_RepresentativeMap
      mergedLiteral representativeLiteral representativeWitness)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_RepresentativeMap
          mergedLiteral representativeLiteral representativeWitness)
        (fun _check rest2 =>
          rest2
            (ay_pehc_RepresentativeMap
              mergedLiteral representativeLiteral representativeWitness)
            (fun rep _tail => rep)))

theorem ay_pehc_hash_equisat
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_Equisat originalCnf hashedCnf := by
  intro accepted
  exact accepted
    (ay_pehc_Equisat originalCnf hashedCnf)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_Equisat originalCnf hashedCnf)
        (fun _check rest2 =>
          rest2
            (ay_pehc_Equisat originalCnf hashedCnf)
            (fun _rep rest3 =>
              rest3
                (ay_pehc_Equisat originalCnf hashedCnf)
                (fun eq _tail => eq))))

theorem ay_pehc_hash_model_reconstruction
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_ModelReconstruction hashedCnf originalCnf hashedModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pehc_ModelReconstruction hashedCnf originalCnf hashedModel originalModel)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_ModelReconstruction
          hashedCnf originalCnf hashedModel originalModel)
        (fun _check rest2 =>
          rest2
            (ay_pehc_ModelReconstruction
              hashedCnf originalCnf hashedModel originalModel)
            (fun _rep rest3 =>
              rest3
                (ay_pehc_ModelReconstruction
                  hashedCnf originalCnf hashedModel originalModel)
                (fun _eq rest4 =>
                  rest4
                    (ay_pehc_ModelReconstruction
                      hashedCnf originalCnf hashedModel originalModel)
                    (fun model _tail => model)))))

theorem ay_pehc_hash_proof_reconstruction
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_ProofReconstruction originalCnf hashedCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pehc_ProofReconstruction originalCnf hashedCnf certificate conflict)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_ProofReconstruction originalCnf hashedCnf certificate conflict)
        (fun _check rest2 =>
          rest2
            (ay_pehc_ProofReconstruction
              originalCnf hashedCnf certificate conflict)
            (fun _rep rest3 =>
              rest3
                (ay_pehc_ProofReconstruction
                  originalCnf hashedCnf certificate conflict)
                (fun _eq rest4 =>
                  rest4
                    (ay_pehc_ProofReconstruction
                      originalCnf hashedCnf certificate conflict)
                    (fun _model rest5 =>
                      rest5
                        (ay_pehc_ProofReconstruction
                          originalCnf hashedCnf certificate conflict)
                        (fun proof _tail => proof))))))

theorem ay_pehc_hash_digest
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_DigestMembership hashDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pehc_DigestMembership hashDigest manifestDigest)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_DigestMembership hashDigest manifestDigest)
        (fun _check rest2 =>
          rest2
            (ay_pehc_DigestMembership hashDigest manifestDigest)
            (fun _rep rest3 =>
              rest3
                (ay_pehc_DigestMembership hashDigest manifestDigest)
                (fun _eq rest4 =>
                  rest4
                    (ay_pehc_DigestMembership hashDigest manifestDigest)
                    (fun _model rest5 =>
                      rest5
                        (ay_pehc_DigestMembership hashDigest manifestDigest)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pehc_DigestMembership hashDigest manifestDigest)
                            (fun digest _tail => digest)))))))

theorem ay_pehc_hash_checker
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_CheckerReplay hashCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pehc_CheckerReplay hashCertificate checkerAccepted)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_CheckerReplay hashCertificate checkerAccepted)
        (fun _check rest2 =>
          rest2
            (ay_pehc_CheckerReplay hashCertificate checkerAccepted)
            (fun _rep rest3 =>
              rest3
                (ay_pehc_CheckerReplay hashCertificate checkerAccepted)
                (fun _eq rest4 =>
                  rest4
                    (ay_pehc_CheckerReplay hashCertificate checkerAccepted)
                    (fun _model rest5 =>
                      rest5
                        (ay_pehc_CheckerReplay hashCertificate checkerAccepted)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pehc_CheckerReplay
                              hashCertificate checkerAccepted)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pehc_CheckerReplay
                                  hashCertificate checkerAccepted)
                                (fun checker _tail => checker))))))))

theorem ay_pehc_hash_fingerprint
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_FingerprintAgreement
      originalFingerprint hashedFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pehc_FingerprintAgreement
      originalFingerprint hashedFingerprint fingerprintWitness)
    (fun _lineage rest1 =>
      rest1
        (ay_pehc_FingerprintAgreement
          originalFingerprint hashedFingerprint fingerprintWitness)
        (fun _check rest2 =>
          rest2
            (ay_pehc_FingerprintAgreement
              originalFingerprint hashedFingerprint fingerprintWitness)
            (fun _rep rest3 =>
              rest3
                (ay_pehc_FingerprintAgreement
                  originalFingerprint hashedFingerprint fingerprintWitness)
                (fun _eq rest4 =>
                  rest4
                    (ay_pehc_FingerprintAgreement
                      originalFingerprint hashedFingerprint fingerprintWitness)
                    (fun _model rest5 =>
                      rest5
                        (ay_pehc_FingerprintAgreement
                          originalFingerprint hashedFingerprint
                          fingerprintWitness)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pehc_FingerprintAgreement
                              originalFingerprint hashedFingerprint
                              fingerprintWitness)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pehc_FingerprintAgreement
                                  originalFingerprint hashedFingerprint
                                  fingerprintWitness)
                                (fun _checker fp => fp))))))))

theorem ay_pehc_sat_pullback
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_Sat hashedCnf hashedModel ->
    ay_pehc_Sat originalCnf originalModel := by
  intro accepted hashedSat
  exact
    (ay_pehc_hash_model_reconstruction
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral representativeLiteral
      representativeWitness hashedModel originalModel certificate conflict
      hashDigest manifestDigest hashCertificate checkerAccepted
      originalFingerprint hashedFingerprint fingerprintWitness accepted)
      hashedSat

theorem ay_pehc_unsat_pushback
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_Replay hashedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pehc_hash_proof_reconstruction
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral representativeLiteral
      representativeWitness hashedModel originalModel certificate conflict
      hashDigest manifestDigest hashCertificate checkerAccepted
      originalFingerprint hashedFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pehc_public_sat
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_Sat hashedCnf hashedModel ->
    exitCode ->
    ay_pehc_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted hashedSat exit
  exact ay_pehc_disj_left
    (ay_pehc_ExitCodeSound exitCode (ay_pehc_Sat originalCnf originalModel))
    (ay_pehc_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pehc_conj_intro exitCode
      (ay_pehc_Sat originalCnf originalModel)
      exit
      (ay_pehc_sat_pullback
        originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
        hashBucket collisionRejected hashWitness mergedLiteral
        representativeLiteral representativeWitness hashedModel originalModel
        certificate conflict hashDigest manifestDigest hashCertificate
        checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness
        accepted hashedSat))

theorem ay_pehc_public_unsat
    (originalCnf : Prop) (hashedCnf : Prop)
    (sourceClasses : Prop) (mergedClasses : Prop)
    (lineageWitness : Prop)
    (hashBucket : Prop) (collisionRejected : Prop) (hashWitness : Prop)
    (mergedLiteral : Prop) (representativeLiteral : Prop)
    (representativeWitness : Prop)
    (hashedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hashDigest : Prop) (manifestDigest : Prop)
    (hashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hashedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pehc_AcceptedHashCongruence
      originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
      hashBucket collisionRejected hashWitness mergedLiteral
      representativeLiteral representativeWitness hashedModel originalModel
      certificate conflict hashDigest manifestDigest hashCertificate
      checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness ->
    ay_pehc_Replay hashedCnf certificate conflict ->
    exitCode ->
    ay_pehc_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pehc_disj_right
    (ay_pehc_ExitCodeSound exitCode (ay_pehc_Sat originalCnf originalModel))
    (ay_pehc_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pehc_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pehc_unsat_pushback
          originalCnf hashedCnf sourceClasses mergedClasses lineageWitness
          hashBucket collisionRejected hashWitness mergedLiteral
          representativeLiteral representativeWitness hashedModel originalModel
          certificate conflict hashDigest manifestDigest hashCertificate
          checkerAccepted originalFingerprint hashedFingerprint fingerprintWitness
          accepted replay cert original))

theorem ay_pehc_failure_hash_collision
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    hashCollision ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro collision
  exact ay_pehc_disj_left hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    collision

theorem ay_pehc_failure_missing_representative
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    missingRepresentative ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro missing
  exact ay_pehc_disj_right hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    (ay_pehc_disj_left missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))))
      missing)

theorem ay_pehc_failure_broken_equivalence_lineage
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    brokenEquivalenceLineage ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro broken
  exact ay_pehc_disj_right hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    (ay_pehc_disj_right missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))))
      (ay_pehc_disj_left brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))
        broken))

theorem ay_pehc_failure_stale_reconstruction
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    staleReconstruction ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro stale
  exact ay_pehc_disj_right hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    (ay_pehc_disj_right missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))))
      (ay_pehc_disj_right brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))
        (ay_pehc_disj_left staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))
          stale)))

theorem ay_pehc_failure_digest_mismatch
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    digestMismatch ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro mismatch
  exact ay_pehc_disj_right hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    (ay_pehc_disj_right missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))))
      (ay_pehc_disj_right brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))
        (ay_pehc_disj_right staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))
          (ay_pehc_disj_left digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)
            mismatch))))

theorem ay_pehc_failure_replay_rejected
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    replayRejected ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro rejected
  exact ay_pehc_disj_right hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    (ay_pehc_disj_right missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))))
      (ay_pehc_disj_right brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))
        (ay_pehc_disj_right staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))
          (ay_pehc_disj_right digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)
            (ay_pehc_disj_left replayRejected fingerprintDrift rejected)))))

theorem ay_pehc_failure_fingerprint_drift
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    fingerprintDrift ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro drift
  exact ay_pehc_disj_right hashCollision
    (ay_pehc_Disj missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))))
    (ay_pehc_disj_right missingRepresentative
      (ay_pehc_Disj brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))))
      (ay_pehc_disj_right brokenEquivalenceLineage
        (ay_pehc_Disj staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)))
        (ay_pehc_disj_right staleReconstruction
          (ay_pehc_Disj digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift))
          (ay_pehc_disj_right digestMismatch
            (ay_pehc_Disj replayRejected fingerprintDrift)
            (ay_pehc_disj_right replayRejected fingerprintDrift drift)))))

theorem ay_pehc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pehc_DiagnosticHashLogEntry
      previousLog nextLog currentCnf hashCollision missingRepresentative
      brokenEquivalenceLineage staleReconstruction digestMismatch
      replayRejected fingerprintDrift recompute diagnostic ->
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro entry
  exact entry
    (ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift)
    (fun _previous rest1 =>
      rest1
        (ay_pehc_HashFailure
          hashCollision missingRepresentative brokenEquivalenceLineage
          staleReconstruction digestMismatch replayRejected fingerprintDrift)
        (fun body _next =>
          body
            (ay_pehc_HashFailure
              hashCollision missingRepresentative brokenEquivalenceLineage
              staleReconstruction digestMismatch replayRejected fingerprintDrift)
            (fun failure _tail => failure)))

theorem ay_pehc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pehc_DiagnosticHashLogEntry
      previousLog nextLog currentCnf hashCollision missingRepresentative
      brokenEquivalenceLineage staleReconstruction digestMismatch
      replayRejected fingerprintDrift recompute diagnostic ->
    ay_pehc_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pehc_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pehc_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pehc_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pehc_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pehc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pehc_DiagnosticHashLogEntry
      previousLog nextLog currentCnf hashCollision missingRepresentative
      brokenEquivalenceLineage staleReconstruction digestMismatch
      replayRejected fingerprintDrift recompute diagnostic ->
    ay_pehc_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pehc_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pehc_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pehc_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pehc_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pehc_failure_no_claim
    (hashCollision : Prop) (missingRepresentative : Prop)
    (brokenEquivalenceLineage : Prop) (staleReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (diagnostic : Prop) :
    ay_pehc_HashFailure
      hashCollision missingRepresentative brokenEquivalenceLineage
      staleReconstruction digestMismatch replayRejected fingerprintDrift ->
    diagnostic ->
    ay_pehc_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
