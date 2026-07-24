-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause reason database snapshot soundness skeleton for ay SAT
-- solving. Snapshots used for implication, restart, and conflict-analysis
-- decisions are performance hints only when reason clauses, watched-literal
-- state, learned ids, activity/LBD metadata, deterministic replay, dependency
-- guards, and public soundness guards agree.

def AyBCRDConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyBCRDDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyBCRDEquisat (before : Prop) (after : Prop) :=
  AyBCRDConj (before -> after) (after -> before)

def AyBCRDSnapshotEvidence
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :=
  AyBCRDConj reasonClauses
    (AyBCRDConj watchedState
      (AyBCRDConj learnedIds
        (AyBCRDConj activityLbdMetadata
          (AyBCRDConj deterministicReplay
            (AyBCRDConj dependencyGuard publicSoundnessGuard)))))

def AyBCRDAgreement
    (reasonMatch : Prop) (watchMatch : Prop)
    (learnedIdMatch : Prop) (metadataMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :=
  AyBCRDConj reasonMatch
    (AyBCRDConj watchMatch
      (AyBCRDConj learnedIdMatch
        (AyBCRDConj metadataMatch
          (AyBCRDConj replayMatch
            (AyBCRDConj dependencyMatch publicGuardMatch)))))

def AyBCRDAcceptedSnapshot
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop) :=
  AyBCRDConj snapshot (AyBCRDConj agreement searchHint)

def AyBCRDOutcome (model : Prop) (conflict : Prop) :=
  AyBCRDDisj model conflict

def AyBCRDPublicReport (outcome : Prop) (formula : Prop) :=
  AyBCRDConj outcome formula

def AyBCRDAcceptedReport (snapshot : Prop) (public : Prop) :=
  AyBCRDConj snapshot public

def AyBCRDNoClaim (diagnostic : Prop) (fallbackPublic : Prop) :=
  AyBCRDConj fallbackPublic diagnostic

theorem ay_bcrd_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyBCRDConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_bcrd_conj_left
    (left : Prop) (right : Prop) :
    AyBCRDConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_bcrd_conj_right
    (left : Prop) (right : Prop) :
    AyBCRDConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_bcrd_disj_left
    (left : Prop) (right : Prop) :
    left -> AyBCRDDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_bcrd_disj_right
    (left : Prop) (right : Prop) :
    right -> AyBCRDDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_bcrd_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyBCRDEquisat before after :=
  fun forward backward =>
    ay_bcrd_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_bcrd_equisat_forward
    (before : Prop) (after : Prop) :
    AyBCRDEquisat before after -> before -> after :=
  fun equisat =>
    ay_bcrd_conj_left (before -> after) (after -> before) equisat

theorem ay_bcrd_equisat_backward
    (before : Prop) (after : Prop) :
    AyBCRDEquisat before after -> after -> before :=
  fun equisat =>
    ay_bcrd_conj_right (before -> after) (after -> before) equisat

theorem ay_bcrd_snapshot_evidence_intro
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    reasonClauses ->
    watchedState ->
    learnedIds ->
    activityLbdMetadata ->
    deterministicReplay ->
    dependencyGuard ->
    publicSoundnessGuard ->
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard :=
  fun reasonH watchH learnedH metadataH replayH dependencyH publicH =>
    ay_bcrd_conj_intro reasonClauses
      (AyBCRDConj watchedState
        (AyBCRDConj learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard)))))
      reasonH
      (ay_bcrd_conj_intro watchedState
        (AyBCRDConj learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard))))
        watchH
        (ay_bcrd_conj_intro learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard)))
          learnedH
          (ay_bcrd_conj_intro activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard))
            metadataH
            (ay_bcrd_conj_intro deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard)
              replayH
              (ay_bcrd_conj_intro dependencyGuard publicSoundnessGuard
                dependencyH publicH)))))

theorem ay_bcrd_snapshot_evidence_reason
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    reasonClauses :=
  fun evidence =>
    ay_bcrd_conj_left reasonClauses
      (AyBCRDConj watchedState
        (AyBCRDConj learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bcrd_snapshot_evidence_tail
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    AyBCRDConj watchedState
      (AyBCRDConj learnedIds
        (AyBCRDConj activityLbdMetadata
          (AyBCRDConj deterministicReplay
            (AyBCRDConj dependencyGuard publicSoundnessGuard)))) :=
  fun evidence =>
    ay_bcrd_conj_right reasonClauses
      (AyBCRDConj watchedState
        (AyBCRDConj learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard)))))
      evidence

theorem ay_bcrd_snapshot_evidence_watch
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    watchedState :=
  fun evidence =>
    ay_bcrd_conj_left watchedState
      (AyBCRDConj learnedIds
        (AyBCRDConj activityLbdMetadata
          (AyBCRDConj deterministicReplay
            (AyBCRDConj dependencyGuard publicSoundnessGuard))))
      (ay_bcrd_snapshot_evidence_tail reasonClauses watchedState
        learnedIds activityLbdMetadata deterministicReplay dependencyGuard
        publicSoundnessGuard evidence)

theorem ay_bcrd_snapshot_evidence_learned
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    learnedIds :=
  fun evidence =>
    ay_bcrd_conj_left learnedIds
      (AyBCRDConj activityLbdMetadata
        (AyBCRDConj deterministicReplay
          (AyBCRDConj dependencyGuard publicSoundnessGuard)))
      (ay_bcrd_conj_right watchedState
        (AyBCRDConj learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard))))
        (ay_bcrd_snapshot_evidence_tail reasonClauses watchedState
          learnedIds activityLbdMetadata deterministicReplay dependencyGuard
          publicSoundnessGuard evidence))

theorem ay_bcrd_snapshot_evidence_metadata
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    activityLbdMetadata :=
  fun evidence =>
    ay_bcrd_conj_left activityLbdMetadata
      (AyBCRDConj deterministicReplay
        (AyBCRDConj dependencyGuard publicSoundnessGuard))
      (ay_bcrd_conj_right learnedIds
        (AyBCRDConj activityLbdMetadata
          (AyBCRDConj deterministicReplay
            (AyBCRDConj dependencyGuard publicSoundnessGuard)))
        (ay_bcrd_conj_right watchedState
          (AyBCRDConj learnedIds
            (AyBCRDConj activityLbdMetadata
              (AyBCRDConj deterministicReplay
                (AyBCRDConj dependencyGuard publicSoundnessGuard))))
          (ay_bcrd_snapshot_evidence_tail reasonClauses watchedState
            learnedIds activityLbdMetadata deterministicReplay
            dependencyGuard publicSoundnessGuard evidence)))

theorem ay_bcrd_snapshot_evidence_replay
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    deterministicReplay :=
  fun evidence =>
    ay_bcrd_conj_left deterministicReplay
      (AyBCRDConj dependencyGuard publicSoundnessGuard)
      (ay_bcrd_conj_right activityLbdMetadata
        (AyBCRDConj deterministicReplay
          (AyBCRDConj dependencyGuard publicSoundnessGuard))
        (ay_bcrd_conj_right learnedIds
          (AyBCRDConj activityLbdMetadata
            (AyBCRDConj deterministicReplay
              (AyBCRDConj dependencyGuard publicSoundnessGuard)))
          (ay_bcrd_conj_right watchedState
            (AyBCRDConj learnedIds
              (AyBCRDConj activityLbdMetadata
                (AyBCRDConj deterministicReplay
                  (AyBCRDConj dependencyGuard publicSoundnessGuard))))
            (ay_bcrd_snapshot_evidence_tail reasonClauses watchedState
              learnedIds activityLbdMetadata deterministicReplay
              dependencyGuard publicSoundnessGuard evidence))))

theorem ay_bcrd_snapshot_evidence_dependency
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    dependencyGuard :=
  fun evidence =>
    ay_bcrd_conj_left dependencyGuard publicSoundnessGuard
      (ay_bcrd_conj_right deterministicReplay
        (AyBCRDConj dependencyGuard publicSoundnessGuard)
        (ay_bcrd_conj_right activityLbdMetadata
          (AyBCRDConj deterministicReplay
            (AyBCRDConj dependencyGuard publicSoundnessGuard))
          (ay_bcrd_conj_right learnedIds
            (AyBCRDConj activityLbdMetadata
              (AyBCRDConj deterministicReplay
                (AyBCRDConj dependencyGuard publicSoundnessGuard)))
            (ay_bcrd_conj_right watchedState
              (AyBCRDConj learnedIds
                (AyBCRDConj activityLbdMetadata
                  (AyBCRDConj deterministicReplay
                    (AyBCRDConj dependencyGuard publicSoundnessGuard))))
              (ay_bcrd_snapshot_evidence_tail reasonClauses watchedState
                learnedIds activityLbdMetadata deterministicReplay
                dependencyGuard publicSoundnessGuard evidence)))))

theorem ay_bcrd_snapshot_evidence_public
    (reasonClauses : Prop) (watchedState : Prop)
    (learnedIds : Prop) (activityLbdMetadata : Prop)
    (deterministicReplay : Prop) (dependencyGuard : Prop)
    (publicSoundnessGuard : Prop) :
    AyBCRDSnapshotEvidence reasonClauses watchedState learnedIds
      activityLbdMetadata deterministicReplay dependencyGuard
      publicSoundnessGuard ->
    publicSoundnessGuard :=
  fun evidence =>
    ay_bcrd_conj_right dependencyGuard publicSoundnessGuard
      (ay_bcrd_conj_right deterministicReplay
        (AyBCRDConj dependencyGuard publicSoundnessGuard)
        (ay_bcrd_conj_right activityLbdMetadata
          (AyBCRDConj deterministicReplay
            (AyBCRDConj dependencyGuard publicSoundnessGuard))
          (ay_bcrd_conj_right learnedIds
            (AyBCRDConj activityLbdMetadata
              (AyBCRDConj deterministicReplay
                (AyBCRDConj dependencyGuard publicSoundnessGuard)))
            (ay_bcrd_conj_right watchedState
              (AyBCRDConj learnedIds
                (AyBCRDConj activityLbdMetadata
                  (AyBCRDConj deterministicReplay
                    (AyBCRDConj dependencyGuard publicSoundnessGuard))))
              (ay_bcrd_snapshot_evidence_tail reasonClauses watchedState
                learnedIds activityLbdMetadata deterministicReplay
                dependencyGuard publicSoundnessGuard evidence)))))

theorem ay_bcrd_agreement_intro
    (reasonMatch : Prop) (watchMatch : Prop)
    (learnedIdMatch : Prop) (metadataMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    reasonMatch ->
    watchMatch ->
    learnedIdMatch ->
    metadataMatch ->
    replayMatch ->
    dependencyMatch ->
    publicGuardMatch ->
    AyBCRDAgreement reasonMatch watchMatch learnedIdMatch
      metadataMatch replayMatch dependencyMatch publicGuardMatch :=
  fun reasonH watchH learnedH metadataH replayH dependencyH publicH =>
    ay_bcrd_conj_intro reasonMatch
      (AyBCRDConj watchMatch
        (AyBCRDConj learnedIdMatch
          (AyBCRDConj metadataMatch
            (AyBCRDConj replayMatch
              (AyBCRDConj dependencyMatch publicGuardMatch)))))
      reasonH
      (ay_bcrd_conj_intro watchMatch
        (AyBCRDConj learnedIdMatch
          (AyBCRDConj metadataMatch
            (AyBCRDConj replayMatch
              (AyBCRDConj dependencyMatch publicGuardMatch))))
        watchH
        (ay_bcrd_conj_intro learnedIdMatch
          (AyBCRDConj metadataMatch
            (AyBCRDConj replayMatch
              (AyBCRDConj dependencyMatch publicGuardMatch)))
          learnedH
          (ay_bcrd_conj_intro metadataMatch
            (AyBCRDConj replayMatch
              (AyBCRDConj dependencyMatch publicGuardMatch))
            metadataH
            (ay_bcrd_conj_intro replayMatch
              (AyBCRDConj dependencyMatch publicGuardMatch)
              replayH
              (ay_bcrd_conj_intro dependencyMatch publicGuardMatch
                dependencyH publicH)))))

theorem ay_bcrd_agreement_reason
    (reasonMatch : Prop) (watchMatch : Prop)
    (learnedIdMatch : Prop) (metadataMatch : Prop)
    (replayMatch : Prop) (dependencyMatch : Prop)
    (publicGuardMatch : Prop) :
    AyBCRDAgreement reasonMatch watchMatch learnedIdMatch
      metadataMatch replayMatch dependencyMatch publicGuardMatch ->
    reasonMatch :=
  fun agreement =>
    ay_bcrd_conj_left reasonMatch
      (AyBCRDConj watchMatch
        (AyBCRDConj learnedIdMatch
          (AyBCRDConj metadataMatch
            (AyBCRDConj replayMatch
              (AyBCRDConj dependencyMatch publicGuardMatch)))))
      agreement

theorem ay_bcrd_accepted_snapshot_intro
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop) :
    snapshot ->
    agreement ->
    searchHint ->
    AyBCRDAcceptedSnapshot snapshot agreement searchHint :=
  fun snapshotH agreementH hintH =>
    ay_bcrd_conj_intro snapshot (AyBCRDConj agreement searchHint)
      snapshotH
      (ay_bcrd_conj_intro agreement searchHint agreementH hintH)

theorem ay_bcrd_accepted_snapshot_snapshot
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop) :
    AyBCRDAcceptedSnapshot snapshot agreement searchHint -> snapshot :=
  fun accepted =>
    ay_bcrd_conj_left snapshot (AyBCRDConj agreement searchHint)
      accepted

theorem ay_bcrd_accepted_snapshot_agreement
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop) :
    AyBCRDAcceptedSnapshot snapshot agreement searchHint -> agreement :=
  fun accepted =>
    ay_bcrd_conj_left agreement searchHint
      (ay_bcrd_conj_right snapshot (AyBCRDConj agreement searchHint)
        accepted)

theorem ay_bcrd_accepted_snapshot_hint
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop) :
    AyBCRDAcceptedSnapshot snapshot agreement searchHint -> searchHint :=
  fun accepted =>
    ay_bcrd_conj_right agreement searchHint
      (ay_bcrd_conj_right snapshot (AyBCRDConj agreement searchHint)
        accepted)

theorem ay_bcrd_public_sat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    model ->
    formula ->
    AyBCRDPublicReport (AyBCRDOutcome model conflict) formula :=
  fun modelH formulaH =>
    ay_bcrd_conj_intro (AyBCRDOutcome model conflict) formula
      (ay_bcrd_disj_left model conflict modelH)
      formulaH

theorem ay_bcrd_public_unsat_report
    (model : Prop) (conflict : Prop) (formula : Prop) :
    conflict ->
    formula ->
    AyBCRDPublicReport (AyBCRDOutcome model conflict) formula :=
  fun conflictH formulaH =>
    ay_bcrd_conj_intro (AyBCRDOutcome model conflict) formula
      (ay_bcrd_disj_right model conflict conflictH)
      formulaH

theorem ay_bcrd_accepted_report_intro
    (snapshot : Prop) (public : Prop) :
    snapshot -> public -> AyBCRDAcceptedReport snapshot public :=
  fun snapshotH publicH =>
    ay_bcrd_conj_intro snapshot public snapshotH publicH

theorem ay_bcrd_accepted_report_public
    (snapshot : Prop) (public : Prop) :
    AyBCRDAcceptedReport snapshot public -> public :=
  fun report =>
    ay_bcrd_conj_right snapshot public report

theorem ay_bcrd_no_claim_intro
    (diagnostic : Prop) (fallbackPublic : Prop) :
    diagnostic ->
    fallbackPublic ->
    AyBCRDNoClaim diagnostic fallbackPublic :=
  fun diagnosticH fallbackH =>
    ay_bcrd_conj_intro fallbackPublic diagnostic fallbackH diagnosticH

theorem ay_bcrd_no_claim_preserves_fallback
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCRDNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcrd_conj_left fallbackPublic diagnostic noClaim

theorem ay_bcrd_stale_reason_no_claim
    (staleReason : Prop) (fallbackPublic : Prop) :
    staleReason ->
    fallbackPublic ->
    AyBCRDNoClaim staleReason fallbackPublic :=
  fun staleH fallbackH =>
    ay_bcrd_no_claim_intro staleReason fallbackPublic staleH fallbackH

theorem ay_bcrd_watch_mismatch_no_claim
    (watchMismatch : Prop) (fallbackPublic : Prop) :
    watchMismatch ->
    fallbackPublic ->
    AyBCRDNoClaim watchMismatch fallbackPublic :=
  fun mismatchH fallbackH =>
    ay_bcrd_no_claim_intro watchMismatch fallbackPublic
      mismatchH fallbackH

theorem ay_bcrd_missing_learned_id_no_claim
    (missingLearnedId : Prop) (fallbackPublic : Prop) :
    missingLearnedId ->
    fallbackPublic ->
    AyBCRDNoClaim missingLearnedId fallbackPublic :=
  fun missingH fallbackH =>
    ay_bcrd_no_claim_intro missingLearnedId fallbackPublic
      missingH fallbackH

theorem ay_bcrd_metadata_drift_no_claim
    (metadataDrift : Prop) (fallbackPublic : Prop) :
    metadataDrift ->
    fallbackPublic ->
    AyBCRDNoClaim metadataDrift fallbackPublic :=
  fun driftH fallbackH =>
    ay_bcrd_no_claim_intro metadataDrift fallbackPublic driftH fallbackH

theorem ay_bcrd_replay_rejection_no_claim
    (replayRejected : Prop) (fallbackPublic : Prop) :
    replayRejected ->
    fallbackPublic ->
    AyBCRDNoClaim replayRejected fallbackPublic :=
  fun rejectedH fallbackH =>
    ay_bcrd_no_claim_intro replayRejected fallbackPublic
      rejectedH fallbackH

theorem ay_bcrd_bad_snapshot_cannot_publish
    (badSnapshot : Prop) (fallbackPublic : Prop) :
    badSnapshot ->
    fallbackPublic ->
    AyBCRDNoClaim badSnapshot fallbackPublic :=
  fun badH fallbackH =>
    ay_bcrd_no_claim_intro badSnapshot fallbackPublic badH fallbackH

theorem ay_bcrd_accepted_snapshot_guides_sat
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    snapshot ->
    agreement ->
    searchHint ->
    model ->
    formula ->
    AyBCRDAcceptedReport
      (AyBCRDAcceptedSnapshot snapshot agreement searchHint)
      (AyBCRDPublicReport (AyBCRDOutcome model conflict) formula) :=
  fun snapshotH agreementH hintH modelH formulaH =>
    ay_bcrd_accepted_report_intro
      (AyBCRDAcceptedSnapshot snapshot agreement searchHint)
      (AyBCRDPublicReport (AyBCRDOutcome model conflict) formula)
      (ay_bcrd_accepted_snapshot_intro snapshot agreement searchHint
        snapshotH agreementH hintH)
      (ay_bcrd_public_sat_report model conflict formula modelH formulaH)

theorem ay_bcrd_accepted_snapshot_guides_unsat
    (snapshot : Prop) (agreement : Prop) (searchHint : Prop)
    (formula : Prop) (model : Prop) (conflict : Prop) :
    snapshot ->
    agreement ->
    searchHint ->
    conflict ->
    formula ->
    AyBCRDAcceptedReport
      (AyBCRDAcceptedSnapshot snapshot agreement searchHint)
      (AyBCRDPublicReport (AyBCRDOutcome model conflict) formula) :=
  fun snapshotH agreementH hintH conflictH formulaH =>
    ay_bcrd_accepted_report_intro
      (AyBCRDAcceptedSnapshot snapshot agreement searchHint)
      (AyBCRDPublicReport (AyBCRDOutcome model conflict) formula)
      (ay_bcrd_accepted_snapshot_intro snapshot agreement searchHint
        snapshotH agreementH hintH)
      (ay_bcrd_public_unsat_report model conflict formula
        conflictH formulaH)

theorem ay_bcrd_accepted_snapshot_report_soundness
    (snapshot : Prop) (formula : Prop) (model : Prop) (conflict : Prop) :
    AyBCRDAcceptedReport snapshot
      (AyBCRDPublicReport (AyBCRDOutcome model conflict) formula) ->
    AyBCRDPublicReport (AyBCRDOutcome model conflict) formula :=
  fun report =>
    ay_bcrd_accepted_report_public snapshot
      (AyBCRDPublicReport (AyBCRDOutcome model conflict) formula)
      report

theorem ay_bcrd_no_claim_recompute_preserves_soundness
    (diagnostic : Prop) (fallbackPublic : Prop) :
    AyBCRDNoClaim diagnostic fallbackPublic -> fallbackPublic :=
  fun noClaim =>
    ay_bcrd_no_claim_preserves_fallback diagnostic fallbackPublic noClaim
