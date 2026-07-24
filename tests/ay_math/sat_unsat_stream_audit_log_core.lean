-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Audit-log entries for UNSAT stream validator reports. Propositions stand for
-- retained stream proof entries, direct recheck entries, unavailable no-claim
-- entries, append-only log preservation, audit digest agreement, and public
-- report outcomes.

def AyUSALConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSALDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSALMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSALEquisat (before : Prop) (after : Prop) :=
  AyUSALConj (before -> after) (after -> before)

def AyUSALStreamProof
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSALConj visibleChunk
    (AyUSALConj
      (AyUSALMap visibleChunk checkpointSnapshot)
      (AyUSALConj
        (AyUSALMap checkpointSnapshot finalAccumulator)
        (AyUSALConj
          (AyUSALMap finalAccumulator emptyClause)
          (AyUSALConj
            (AyUSALMap emptyClause visibleUnsat)
            (AyUSALMap visibleUnsat originalUnsat)))))

def AyUSALRetainedLogEntry
    (auditDigest : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSALConj auditDigest
    (AyUSALConj acceptedReport
      (AyUSALStreamProof visibleChunk checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat))

def AyUSALDirectLogEntry
    (auditDigest : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSALRetainedLogEntry auditDigest acceptedReport visibleChunk
    checkpointSnapshot finalAccumulator emptyClause visibleUnsat originalUnsat

def AyUSALUnavailableLogEntry
    (auditDigest : Prop) (fallbackNoClaim : Prop)
    (missingEntry : Prop) (evictedEntry : Prop) :=
  AyUSALConj auditDigest
    (AyUSALConj fallbackNoClaim
      (AyUSALDisj missingEntry evictedEntry))

def AyUSALAppendOnly
    (oldLog : Prop) (newEntry : Prop) (newLog : Prop) :=
  AyUSALConj oldLog
    (AyUSALConj newEntry
      (AyUSALMap oldLog newLog))

def AyUSALDigestAgreement
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) :=
  AyUSALConj entryDigest
    (AyUSALConj reportDigest digestMatches)

def AyUSALPublicReport
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :=
  AyUSALDisj fallbackNoClaim originalUnsat

def AyUSALRetainedAppendReport
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSALConj
    (AyUSALAppendOnly oldLog
      (AyUSALRetainedLogEntry entryDigest acceptedReport visibleChunk
        checkpointSnapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat)
      newLog)
    (AyUSALConj
      (AyUSALDigestAgreement entryDigest reportDigest digestMatches)
      (AyUSALRetainedLogEntry entryDigest acceptedReport visibleChunk
        checkpointSnapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat))

def AyUSALDirectAppendReport
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSALConj
    (AyUSALAppendOnly oldLog
      (AyUSALDirectLogEntry entryDigest acceptedReport visibleChunk
        checkpointSnapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat)
      newLog)
    (AyUSALConj
      (AyUSALDigestAgreement entryDigest reportDigest digestMatches)
      (AyUSALDirectLogEntry entryDigest acceptedReport visibleChunk
        checkpointSnapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat))

def AyUSALUnavailableAppendReport
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (fallbackNoClaim : Prop)
    (missingEntry : Prop) (evictedEntry : Prop) :=
  AyUSALConj
    (AyUSALAppendOnly oldLog
      (AyUSALUnavailableLogEntry entryDigest fallbackNoClaim missingEntry
        evictedEntry)
      newLog)
    (AyUSALConj
      (AyUSALDigestAgreement entryDigest reportDigest digestMatches)
      (AyUSALUnavailableLogEntry entryDigest fallbackNoClaim missingEntry
        evictedEntry))

theorem ay_usal_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSALConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usal_conj_left
    (p : Prop) (q : Prop) :
    AyUSALConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usal_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSALDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usal_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSALDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usal_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSALEquisat before after := by
  intro forward
  intro backward
  exact ay_usal_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_usal_stream_original_unsat
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALStreamProof visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  exact proof originalUnsat
    (fun hvisible tail =>
      tail originalUnsat
        (fun visible_to_checkpoint tail2 =>
          tail2 originalUnsat
            (fun checkpoint_to_final tail3 =>
              tail3 originalUnsat
                (fun final_to_empty tail4 =>
                  tail4 originalUnsat
                    (fun empty_to_unsat unsat_to_original =>
                      unsat_to_original
                        (empty_to_unsat
                          (final_to_empty
                            (checkpoint_to_final
                              (visible_to_checkpoint hvisible)))))))))))

theorem ay_usal_retained_entry_digest
    (auditDigest : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALRetainedLogEntry auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    auditDigest := by
  intro entry
  exact ay_usal_conj_left auditDigest
    (AyUSALConj acceptedReport
      (AyUSALStreamProof visibleChunk checkpointSnapshot finalAccumulator
        emptyClause visibleUnsat originalUnsat))
    entry

theorem ay_usal_retained_entry_accepted
    (auditDigest : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALRetainedLogEntry auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    acceptedReport := by
  intro entry
  exact entry acceptedReport
    (fun _digest tail =>
      tail acceptedReport
        (fun accepted _proof => accepted))

theorem ay_usal_retained_entry_proof
    (auditDigest : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALRetainedLogEntry auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    AyUSALStreamProof visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat := by
  intro entry
  exact entry
    (AyUSALStreamProof visibleChunk checkpointSnapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat)
    (fun _digest tail =>
      tail
        (AyUSALStreamProof visibleChunk checkpointSnapshot finalAccumulator
          emptyClause visibleUnsat originalUnsat)
        (fun _accepted proof => proof))

theorem ay_usal_retained_entry_original_unsat
    (auditDigest : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALRetainedLogEntry auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro entry
  exact ay_usal_stream_original_unsat
    visibleChunk checkpointSnapshot finalAccumulator emptyClause
    visibleUnsat originalUnsat
    (ay_usal_retained_entry_proof auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat entry)

theorem ay_usal_append_old_log
    (oldLog : Prop) (newEntry : Prop) (newLog : Prop) :
    AyUSALAppendOnly oldLog newEntry newLog ->
    oldLog := by
  intro append
  exact ay_usal_conj_left oldLog
    (AyUSALConj newEntry (oldLog -> newLog))
    append

theorem ay_usal_append_entry
    (oldLog : Prop) (newEntry : Prop) (newLog : Prop) :
    AyUSALAppendOnly oldLog newEntry newLog ->
    newEntry := by
  intro append
  exact append newEntry
    (fun _old tail =>
      tail newEntry
        (fun entry _old_to_new => entry))

theorem ay_usal_append_new_log
    (oldLog : Prop) (newEntry : Prop) (newLog : Prop) :
    AyUSALAppendOnly oldLog newEntry newLog ->
    newLog := by
  intro append
  exact append newLog
    (fun old tail =>
      tail newLog
        (fun _entry old_to_new => old_to_new old))

theorem ay_usal_digest_entry
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) :
    AyUSALDigestAgreement entryDigest reportDigest digestMatches ->
    entryDigest := by
  intro agreement
  exact ay_usal_conj_left entryDigest
    (AyUSALConj reportDigest digestMatches)
    agreement

theorem ay_usal_digest_report
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) :
    AyUSALDigestAgreement entryDigest reportDigest digestMatches ->
    reportDigest := by
  intro agreement
  exact agreement reportDigest
    (fun _entry tail =>
      tail reportDigest
        (fun report _matches => report))

theorem ay_usal_digest_matches
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) :
    AyUSALDigestAgreement entryDigest reportDigest digestMatches ->
    digestMatches := by
  intro agreement
  exact agreement digestMatches
    (fun _entry tail =>
      tail digestMatches
        (fun _report matches => matches))

theorem ay_usal_report_unsat
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUSALPublicReport fallbackNoClaim originalUnsat := by
  intro unsat
  exact ay_usal_disj_right fallbackNoClaim originalUnsat unsat

theorem ay_usal_report_no_claim
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    fallbackNoClaim ->
    AyUSALPublicReport fallbackNoClaim originalUnsat := by
  intro no_claim
  exact ay_usal_disj_left fallbackNoClaim originalUnsat no_claim

theorem ay_usal_retained_append_entry
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALRetainedAppendReport oldLog newLog entryDigest reportDigest
      digestMatches acceptedReport visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    AyUSALRetainedLogEntry entryDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat := by
  intro report
  exact report
    (AyUSALRetainedLogEntry entryDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat)
    (fun _append tail =>
      tail
        (AyUSALRetainedLogEntry entryDigest acceptedReport visibleChunk
          checkpointSnapshot finalAccumulator emptyClause visibleUnsat
          originalUnsat)
        (fun _digest entry => entry))

theorem ay_usal_retained_append_digest
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALRetainedAppendReport oldLog newLog entryDigest reportDigest
      digestMatches acceptedReport visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    AyUSALDigestAgreement entryDigest reportDigest digestMatches := by
  intro report
  exact report
    (AyUSALDigestAgreement entryDigest reportDigest digestMatches)
    (fun _append tail =>
      tail (AyUSALDigestAgreement entryDigest reportDigest digestMatches)
        (fun digest _entry => digest))

theorem ay_usal_retained_append_preserves_unsat_soundness
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (fallbackNoClaim : Prop) :
    AyUSALRetainedAppendReport oldLog newLog entryDigest reportDigest
      digestMatches acceptedReport visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    AyUSALPublicReport fallbackNoClaim originalUnsat := by
  intro report
  exact ay_usal_report_unsat fallbackNoClaim originalUnsat
    (ay_usal_retained_entry_original_unsat entryDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat
      (ay_usal_retained_append_entry oldLog newLog entryDigest reportDigest
        digestMatches acceptedReport visibleChunk checkpointSnapshot
        finalAccumulator emptyClause visibleUnsat originalUnsat report))

theorem ay_usal_direct_append_entry
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSALDirectAppendReport oldLog newLog entryDigest reportDigest
      digestMatches acceptedReport visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    AyUSALDirectLogEntry entryDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat := by
  intro report
  exact report
    (AyUSALDirectLogEntry entryDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat)
    (fun _append tail =>
      tail
        (AyUSALDirectLogEntry entryDigest acceptedReport visibleChunk
          checkpointSnapshot finalAccumulator emptyClause visibleUnsat
          originalUnsat)
        (fun _digest entry => entry))

theorem ay_usal_direct_append_preserves_unsat_soundness
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (fallbackNoClaim : Prop) :
    AyUSALDirectAppendReport oldLog newLog entryDigest reportDigest
      digestMatches acceptedReport visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    AyUSALPublicReport fallbackNoClaim originalUnsat := by
  intro report
  exact ay_usal_report_unsat fallbackNoClaim originalUnsat
    (ay_usal_retained_entry_original_unsat entryDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat
      (ay_usal_direct_append_entry oldLog newLog entryDigest reportDigest
        digestMatches acceptedReport visibleChunk checkpointSnapshot
        finalAccumulator emptyClause visibleUnsat originalUnsat report))

theorem ay_usal_unavailable_entry_no_claim
    (auditDigest : Prop) (fallbackNoClaim : Prop)
    (missingEntry : Prop) (evictedEntry : Prop) :
    AyUSALUnavailableLogEntry auditDigest fallbackNoClaim missingEntry
      evictedEntry ->
    fallbackNoClaim := by
  intro entry
  exact entry fallbackNoClaim
    (fun _digest tail =>
      tail fallbackNoClaim
        (fun no_claim _state => no_claim))

theorem ay_usal_unavailable_append_entry
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (fallbackNoClaim : Prop)
    (missingEntry : Prop) (evictedEntry : Prop) :
    AyUSALUnavailableAppendReport oldLog newLog entryDigest reportDigest
      digestMatches fallbackNoClaim missingEntry evictedEntry ->
    AyUSALUnavailableLogEntry entryDigest fallbackNoClaim missingEntry
      evictedEntry := by
  intro report
  exact report
    (AyUSALUnavailableLogEntry entryDigest fallbackNoClaim missingEntry
      evictedEntry)
    (fun _append tail =>
      tail
        (AyUSALUnavailableLogEntry entryDigest fallbackNoClaim missingEntry
          evictedEntry)
        (fun _digest entry => entry))

theorem ay_usal_unavailable_append_remains_no_claim
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (fallbackNoClaim : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (originalUnsat : Prop) :
    AyUSALUnavailableAppendReport oldLog newLog entryDigest reportDigest
      digestMatches fallbackNoClaim missingEntry evictedEntry ->
    AyUSALPublicReport fallbackNoClaim originalUnsat := by
  intro report
  exact ay_usal_report_no_claim fallbackNoClaim originalUnsat
    (ay_usal_unavailable_entry_no_claim entryDigest fallbackNoClaim
      missingEntry evictedEntry
      (ay_usal_unavailable_append_entry oldLog newLog entryDigest
        reportDigest digestMatches fallbackNoClaim missingEntry evictedEntry
        report))

theorem ay_usal_unavailable_append_blocks_unsat_claim
    (oldLog : Prop) (newLog : Prop)
    (entryDigest : Prop) (reportDigest : Prop)
    (digestMatches : Prop) (fallbackNoClaim : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (originalUnsat : Prop) :
    AyUSALUnavailableAppendReport oldLog newLog entryDigest reportDigest
      digestMatches fallbackNoClaim missingEntry evictedEntry ->
    (fallbackNoClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro report
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_usal_unavailable_entry_no_claim entryDigest fallbackNoClaim
      missingEntry evictedEntry
      (ay_usal_unavailable_append_entry oldLog newLog entryDigest
        reportDigest digestMatches fallbackNoClaim missingEntry evictedEntry
        report))
    unsat
