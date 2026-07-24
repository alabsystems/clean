-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-renumbering map soundness for preprocessing. The propositions
-- stand for old-to-new maps, inverse maps, eliminated/default variable
-- reconstruction, clause ID lineage, model/proof replay hooks, digest
-- membership, original-instance fingerprint agreement, diagnostics, and
-- public SAT/UNSAT reports.

def ay_pvrm_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pvrm_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pvrm_Equisat (before : Prop) (after : Prop) :=
  ay_pvrm_Conj (before -> after) (after -> before)

def ay_pvrm_Sat (cnf : Prop) (model : Prop) :=
  ay_pvrm_Conj cnf model

def ay_pvrm_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pvrm_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pvrm_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pvrm_OldToNewMap
    (oldVars : Prop) (newVars : Prop) (mapWitness : Prop) :=
  ay_pvrm_Conj mapWitness (oldVars -> newVars)

def ay_pvrm_InverseMap
    (newVars : Prop) (oldVars : Prop) (inverseWitness : Prop) :=
  ay_pvrm_Conj inverseWitness (newVars -> oldVars)

def ay_pvrm_BijectionEvidence
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop) :=
  ay_pvrm_Conj
    (ay_pvrm_OldToNewMap oldVars newVars mapWitness)
    (ay_pvrm_InverseMap newVars oldVars inverseWitness)

def ay_pvrm_DefaultReconstruction
    (eliminatedDefaults : Prop) (defaultWitness : Prop) :=
  ay_pvrm_Conj eliminatedDefaults defaultWitness

def ay_pvrm_ClauseLineage
    (oldClauseIds : Prop) (newClauseIds : Prop) (lineageWitness : Prop) :=
  ay_pvrm_Conj lineageWitness
    (ay_pvrm_IdMatch oldClauseIds newClauseIds)

def ay_pvrm_ModelReplayHook
    (renumberedCnf : Prop) (originalCnf : Prop)
    (renumberedModel : Prop) (originalModel : Prop) :=
  ay_pvrm_Sat renumberedCnf renumberedModel ->
    ay_pvrm_Sat originalCnf originalModel

def ay_pvrm_ProofReplayHook
    (originalCnf : Prop) (renumberedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pvrm_Replay renumberedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pvrm_DigestMembership
    (mapDigest : Prop) (manifestDigest : Prop) :=
  ay_pvrm_Conj mapDigest manifestDigest

def ay_pvrm_CheckerReplay
    (renumberingCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pvrm_Conj renumberingCertificate checkerAccepted

def ay_pvrm_FingerprintAgreement
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pvrm_Conj fingerprintWitness
    (ay_pvrm_IdMatch originalFingerprint renumberedFingerprint)

def ay_pvrm_AcceptedRenumbering
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pvrm_Conj
    (ay_pvrm_BijectionEvidence oldVars newVars mapWitness inverseWitness)
    (ay_pvrm_Conj
      (ay_pvrm_DefaultReconstruction eliminatedDefaults defaultWitness)
      (ay_pvrm_Conj
        (ay_pvrm_ClauseLineage oldClauseIds newClauseIds lineageWitness)
        (ay_pvrm_Conj
          (ay_pvrm_Equisat originalCnf renumberedCnf)
          (ay_pvrm_Conj
            (ay_pvrm_ModelReplayHook
              renumberedCnf originalCnf renumberedModel originalModel)
            (ay_pvrm_Conj
              (ay_pvrm_ProofReplayHook
                originalCnf renumberedCnf certificate conflict)
              (ay_pvrm_Conj
                (ay_pvrm_DigestMembership mapDigest manifestDigest)
                (ay_pvrm_Conj
                  (ay_pvrm_CheckerReplay
                    renumberingCertificate checkerAccepted)
                  (ay_pvrm_FingerprintAgreement
                    originalFingerprint renumberedFingerprint
                    fingerprintWitness))))))))

def ay_pvrm_AcceptedRenumberingLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pvrm_Conj previousLog
    (ay_pvrm_Conj
      (ay_pvrm_AcceptedRenumbering
        originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
        eliminatedDefaults defaultWitness oldClauseIds newClauseIds
        lineageWitness renumberedModel originalModel certificate conflict
        mapDigest manifestDigest renumberingCertificate checkerAccepted
        originalFingerprint renumberedFingerprint fingerprintWitness)
      nextLog)

def ay_pvrm_RenumberingFailure
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :=
  ay_pvrm_Disj nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))

def ay_pvrm_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pvrm_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pvrm_Conj currentCnf recompute

def ay_pvrm_DiagnosticRenumberingLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pvrm_Conj previousLog
    (ay_pvrm_Conj
      (ay_pvrm_Conj
        (ay_pvrm_RenumberingFailure
          nonBijectiveMap missingInverseEvidence staleClauseLineage
          digestMismatch replayRejected fingerprintDrift)
        (ay_pvrm_Conj
          (ay_pvrm_RecomputeObligation currentCnf recompute)
          (ay_pvrm_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pvrm_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pvrm_Conj exitCode claim

def ay_pvrm_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pvrm_Disj
    (ay_pvrm_ExitCodeSound exitCode (ay_pvrm_Sat originalCnf model))
    (ay_pvrm_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pvrm_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pvrm_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pvrm_conj_left
    (left : Prop) (right : Prop) :
    ay_pvrm_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pvrm_conj_right
    (left : Prop) (right : Prop) :
    ay_pvrm_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pvrm_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pvrm_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pvrm_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pvrm_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pvrm_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pvrm_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pvrm_conj_left (before -> after) (after -> before) eq

theorem ay_pvrm_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pvrm_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pvrm_conj_right (before -> after) (after -> before) eq

theorem ay_pvrm_renumbering_bijection
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_BijectionEvidence oldVars newVars mapWitness inverseWitness := by
  intro accepted
  exact ay_pvrm_conj_left
    (ay_pvrm_BijectionEvidence oldVars newVars mapWitness inverseWitness)
    (ay_pvrm_Conj
      (ay_pvrm_DefaultReconstruction eliminatedDefaults defaultWitness)
      (ay_pvrm_Conj
        (ay_pvrm_ClauseLineage oldClauseIds newClauseIds lineageWitness)
        (ay_pvrm_Conj
          (ay_pvrm_Equisat originalCnf renumberedCnf)
          (ay_pvrm_Conj
            (ay_pvrm_ModelReplayHook
              renumberedCnf originalCnf renumberedModel originalModel)
            (ay_pvrm_Conj
              (ay_pvrm_ProofReplayHook
                originalCnf renumberedCnf certificate conflict)
              (ay_pvrm_Conj
                (ay_pvrm_DigestMembership mapDigest manifestDigest)
                (ay_pvrm_Conj
                  (ay_pvrm_CheckerReplay
                    renumberingCertificate checkerAccepted)
                  (ay_pvrm_FingerprintAgreement
                    originalFingerprint renumberedFingerprint
                    fingerprintWitness))))))))
    accepted

theorem ay_pvrm_renumbering_defaults
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_DefaultReconstruction eliminatedDefaults defaultWitness := by
  intro accepted
  exact accepted
    (ay_pvrm_DefaultReconstruction eliminatedDefaults defaultWitness)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_DefaultReconstruction eliminatedDefaults defaultWitness)
        (fun defaults _tail => defaults))

theorem ay_pvrm_renumbering_clause_lineage
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_ClauseLineage oldClauseIds newClauseIds lineageWitness := by
  intro accepted
  exact accepted
    (ay_pvrm_ClauseLineage oldClauseIds newClauseIds lineageWitness)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_ClauseLineage oldClauseIds newClauseIds lineageWitness)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_ClauseLineage oldClauseIds newClauseIds lineageWitness)
            (fun lineage _tail => lineage)))

theorem ay_pvrm_renumbering_equisat
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_Equisat originalCnf renumberedCnf := by
  intro accepted
  exact accepted
    (ay_pvrm_Equisat originalCnf renumberedCnf)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_Equisat originalCnf renumberedCnf)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_Equisat originalCnf renumberedCnf)
            (fun _lineage rest3 =>
              rest3
                (ay_pvrm_Equisat originalCnf renumberedCnf)
                (fun eq _tail => eq))))

theorem ay_pvrm_renumbering_model_hook
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_ModelReplayHook
      renumberedCnf originalCnf renumberedModel originalModel := by
  intro accepted
  exact accepted
    (ay_pvrm_ModelReplayHook
      renumberedCnf originalCnf renumberedModel originalModel)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_ModelReplayHook
          renumberedCnf originalCnf renumberedModel originalModel)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_ModelReplayHook
              renumberedCnf originalCnf renumberedModel originalModel)
            (fun _lineage rest3 =>
              rest3
                (ay_pvrm_ModelReplayHook
                  renumberedCnf originalCnf renumberedModel originalModel)
                (fun _eq rest4 =>
                  rest4
                    (ay_pvrm_ModelReplayHook
                      renumberedCnf originalCnf renumberedModel originalModel)
                    (fun model _tail => model)))))

theorem ay_pvrm_renumbering_proof_hook
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_ProofReplayHook originalCnf renumberedCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pvrm_ProofReplayHook originalCnf renumberedCnf certificate conflict)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_ProofReplayHook originalCnf renumberedCnf certificate conflict)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_ProofReplayHook
              originalCnf renumberedCnf certificate conflict)
            (fun _lineage rest3 =>
              rest3
                (ay_pvrm_ProofReplayHook
                  originalCnf renumberedCnf certificate conflict)
                (fun _eq rest4 =>
                  rest4
                    (ay_pvrm_ProofReplayHook
                      originalCnf renumberedCnf certificate conflict)
                    (fun _model rest5 =>
                      rest5
                        (ay_pvrm_ProofReplayHook
                          originalCnf renumberedCnf certificate conflict)
                        (fun proof _tail => proof))))))

theorem ay_pvrm_renumbering_digest
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_DigestMembership mapDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pvrm_DigestMembership mapDigest manifestDigest)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_DigestMembership mapDigest manifestDigest)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_DigestMembership mapDigest manifestDigest)
            (fun _lineage rest3 =>
              rest3
                (ay_pvrm_DigestMembership mapDigest manifestDigest)
                (fun _eq rest4 =>
                  rest4
                    (ay_pvrm_DigestMembership mapDigest manifestDigest)
                    (fun _model rest5 =>
                      rest5
                        (ay_pvrm_DigestMembership mapDigest manifestDigest)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pvrm_DigestMembership mapDigest manifestDigest)
                            (fun digest _tail => digest)))))))

theorem ay_pvrm_renumbering_checker
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_CheckerReplay renumberingCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pvrm_CheckerReplay renumberingCertificate checkerAccepted)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_CheckerReplay renumberingCertificate checkerAccepted)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_CheckerReplay renumberingCertificate checkerAccepted)
            (fun _lineage rest3 =>
              rest3
                (ay_pvrm_CheckerReplay renumberingCertificate checkerAccepted)
                (fun _eq rest4 =>
                  rest4
                    (ay_pvrm_CheckerReplay
                      renumberingCertificate checkerAccepted)
                    (fun _model rest5 =>
                      rest5
                        (ay_pvrm_CheckerReplay
                          renumberingCertificate checkerAccepted)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pvrm_CheckerReplay
                              renumberingCertificate checkerAccepted)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pvrm_CheckerReplay
                                  renumberingCertificate checkerAccepted)
                                (fun checker _tail => checker))))))))

theorem ay_pvrm_renumbering_fingerprint
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_FingerprintAgreement
      originalFingerprint renumberedFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pvrm_FingerprintAgreement
      originalFingerprint renumberedFingerprint fingerprintWitness)
    (fun _bijection rest1 =>
      rest1
        (ay_pvrm_FingerprintAgreement
          originalFingerprint renumberedFingerprint fingerprintWitness)
        (fun _defaults rest2 =>
          rest2
            (ay_pvrm_FingerprintAgreement
              originalFingerprint renumberedFingerprint fingerprintWitness)
            (fun _lineage rest3 =>
              rest3
                (ay_pvrm_FingerprintAgreement
                  originalFingerprint renumberedFingerprint fingerprintWitness)
                (fun _eq rest4 =>
                  rest4
                    (ay_pvrm_FingerprintAgreement
                      originalFingerprint renumberedFingerprint
                      fingerprintWitness)
                    (fun _model rest5 =>
                      rest5
                        (ay_pvrm_FingerprintAgreement
                          originalFingerprint renumberedFingerprint
                          fingerprintWitness)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pvrm_FingerprintAgreement
                              originalFingerprint renumberedFingerprint
                              fingerprintWitness)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pvrm_FingerprintAgreement
                                  originalFingerprint renumberedFingerprint
                                  fingerprintWitness)
                                (fun _checker fp => fp))))))))

theorem ay_pvrm_sat_pullback
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_Sat renumberedCnf renumberedModel ->
    ay_pvrm_Sat originalCnf originalModel := by
  intro accepted renumberedSat
  exact
    (ay_pvrm_renumbering_model_hook
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness accepted)
      renumberedSat

theorem ay_pvrm_unsat_pushback
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_Replay renumberedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pvrm_renumbering_proof_hook
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pvrm_public_sat
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_Sat renumberedCnf renumberedModel ->
    exitCode ->
    ay_pvrm_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted renumberedSat exit
  exact ay_pvrm_disj_left
    (ay_pvrm_ExitCodeSound exitCode (ay_pvrm_Sat originalCnf originalModel))
    (ay_pvrm_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pvrm_conj_intro exitCode
      (ay_pvrm_Sat originalCnf originalModel)
      exit
      (ay_pvrm_sat_pullback
        originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
        eliminatedDefaults defaultWitness oldClauseIds newClauseIds
        lineageWitness renumberedModel originalModel certificate conflict
        mapDigest manifestDigest renumberingCertificate checkerAccepted
        originalFingerprint renumberedFingerprint fingerprintWitness accepted
        renumberedSat))

theorem ay_pvrm_public_unsat
    (originalCnf : Prop) (renumberedCnf : Prop)
    (oldVars : Prop) (newVars : Prop)
    (mapWitness : Prop) (inverseWitness : Prop)
    (eliminatedDefaults : Prop) (defaultWitness : Prop)
    (oldClauseIds : Prop) (newClauseIds : Prop)
    (lineageWitness : Prop)
    (renumberedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (mapDigest : Prop) (manifestDigest : Prop)
    (renumberingCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (renumberedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pvrm_AcceptedRenumbering
      originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
      eliminatedDefaults defaultWitness oldClauseIds newClauseIds
      lineageWitness renumberedModel originalModel certificate conflict
      mapDigest manifestDigest renumberingCertificate checkerAccepted
      originalFingerprint renumberedFingerprint fingerprintWitness ->
    ay_pvrm_Replay renumberedCnf certificate conflict ->
    exitCode ->
    ay_pvrm_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pvrm_disj_right
    (ay_pvrm_ExitCodeSound exitCode (ay_pvrm_Sat originalCnf originalModel))
    (ay_pvrm_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pvrm_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pvrm_unsat_pushback
          originalCnf renumberedCnf oldVars newVars mapWitness inverseWitness
          eliminatedDefaults defaultWitness oldClauseIds newClauseIds
          lineageWitness renumberedModel originalModel certificate conflict
          mapDigest manifestDigest renumberingCertificate checkerAccepted
          originalFingerprint renumberedFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_pvrm_failure_non_bijective_map
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    nonBijectiveMap ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro non_bijective
  exact ay_pvrm_disj_left nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))
    non_bijective

theorem ay_pvrm_failure_missing_inverse
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    missingInverseEvidence ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro missing
  exact ay_pvrm_disj_right nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))
    (ay_pvrm_disj_left missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)))
      missing)

theorem ay_pvrm_failure_stale_clause_lineage
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    staleClauseLineage ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro stale
  exact ay_pvrm_disj_right nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))
    (ay_pvrm_disj_right missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)))
      (ay_pvrm_disj_left staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))
        stale))

theorem ay_pvrm_failure_digest_mismatch
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    digestMismatch ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro mismatch
  exact ay_pvrm_disj_right nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))
    (ay_pvrm_disj_right missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)))
      (ay_pvrm_disj_right staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))
        (ay_pvrm_disj_left digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)
          mismatch)))

theorem ay_pvrm_failure_replay_rejected
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    replayRejected ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro rejected
  exact ay_pvrm_disj_right nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))
    (ay_pvrm_disj_right missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)))
      (ay_pvrm_disj_right staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))
        (ay_pvrm_disj_right digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)
          (ay_pvrm_disj_left replayRejected fingerprintDrift rejected))))

theorem ay_pvrm_failure_fingerprint_drift
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    fingerprintDrift ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro drift
  exact ay_pvrm_disj_right nonBijectiveMap
    (ay_pvrm_Disj missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))))
    (ay_pvrm_disj_right missingInverseEvidence
      (ay_pvrm_Disj staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)))
      (ay_pvrm_disj_right staleClauseLineage
        (ay_pvrm_Disj digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift))
        (ay_pvrm_disj_right digestMismatch
          (ay_pvrm_Disj replayRejected fingerprintDrift)
          (ay_pvrm_disj_right replayRejected fingerprintDrift drift))))

theorem ay_pvrm_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pvrm_DiagnosticRenumberingLogEntry
      previousLog nextLog currentCnf nonBijectiveMap missingInverseEvidence
      staleClauseLineage digestMismatch replayRejected fingerprintDrift
      recompute diagnostic ->
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift := by
  intro entry
  exact entry
    (ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift)
    (fun _previous rest1 =>
      rest1
        (ay_pvrm_RenumberingFailure
          nonBijectiveMap missingInverseEvidence staleClauseLineage
          digestMismatch replayRejected fingerprintDrift)
        (fun body _next =>
          body
            (ay_pvrm_RenumberingFailure
              nonBijectiveMap missingInverseEvidence staleClauseLineage
              digestMismatch replayRejected fingerprintDrift)
            (fun failure _tail => failure)))

theorem ay_pvrm_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pvrm_DiagnosticRenumberingLogEntry
      previousLog nextLog currentCnf nonBijectiveMap missingInverseEvidence
      staleClauseLineage digestMismatch replayRejected fingerprintDrift
      recompute diagnostic ->
    ay_pvrm_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pvrm_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pvrm_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pvrm_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pvrm_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pvrm_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pvrm_DiagnosticRenumberingLogEntry
      previousLog nextLog currentCnf nonBijectiveMap missingInverseEvidence
      staleClauseLineage digestMismatch replayRejected fingerprintDrift
      recompute diagnostic ->
    ay_pvrm_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pvrm_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pvrm_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pvrm_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pvrm_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pvrm_failure_no_claim
    (nonBijectiveMap : Prop) (missingInverseEvidence : Prop)
    (staleClauseLineage : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (diagnostic : Prop) :
    ay_pvrm_RenumberingFailure
      nonBijectiveMap missingInverseEvidence staleClauseLineage
      digestMismatch replayRejected fingerprintDrift ->
    diagnostic ->
    ay_pvrm_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
