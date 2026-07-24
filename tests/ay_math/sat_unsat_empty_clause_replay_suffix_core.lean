-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded empty-clause replay suffix soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for compact replay suffixes,
-- parent coverage, antecedent retention, checker transcripts, epoch/digest
-- membership, reconstruction handles, original fingerprints, and fail-closed
-- no-claim/recompute diagnostics.

def AyUECRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUECRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUECRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUECRSuffixParents
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :=
  AyUECRConj
    (AyUECRMap replaySuffix parentCoverage)
    (AyUECRMap parentCoverage emptyClause)

def AyUECRAntecedentRetention
    (replaySuffix : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) :=
  AyUECRConj
    (AyUECRMap replaySuffix antecedentRetention)
    (AyUECRMap antecedentRetention retentionAccepted)

def AyUECRCheckerTranscript
    (replaySuffix : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUECRConj
    (AyUECRMap replaySuffix checkerTranscript)
    (AyUECRMap checkerTranscript checkerAccepted)

def AyUECREpochDigest
    (replaySuffix : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :=
  AyUECRConj
    (AyUECRMap replaySuffix epochMember)
    (AyUECRConj
      (AyUECRMap epochMember digestMember)
      (AyUECRMap digestMember epochDigestAccepted))

def AyUECRReconstruction
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUECRConj reconstructionHandle
    (AyUECRConj
      (AyUECRMap emptyClause visibleUnsat)
      (AyUECRMap visibleUnsat originalUnsat))

def AyUECRFingerprint
    (replaySuffix : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :=
  AyUECRConj
    (AyUECRMap replaySuffix fingerprintAgrees)
    (AyUECRMap fingerprintAgrees visibleUnsat)

def AyUECRAcceptedEvidence
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUECRConj replaySuffix
    (AyUECRConj
      (AyUECRSuffixParents replaySuffix parentCoverage emptyClause)
      (AyUECRConj
        (AyUECRAntecedentRetention replaySuffix antecedentRetention
          retentionAccepted)
        (AyUECRConj
          (AyUECRCheckerTranscript replaySuffix checkerTranscript
            checkerAccepted)
          (AyUECRConj
            (AyUECREpochDigest replaySuffix epochMember digestMember
              epochDigestAccepted)
            (AyUECRConj
              (AyUECRReconstruction emptyClause reconstructionHandle
                visibleUnsat originalUnsat)
              (AyUECRFingerprint replaySuffix fingerprintAgrees
                visibleUnsat))))))

def AyUECRAcceptedSuffix
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUECRConj
    (AyUECRAcceptedEvidence replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat

def AyUECRBadSuffix
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUECRConj
    (AyUECRConj noClaim recompute)
    (AyUECRDisj missingParentCoverage
      (AyUECRDisj incorrectParentCoverage
        (AyUECRDisj missingAntecedentRetention
          (AyUECRDisj checkerRejected
            (AyUECRDisj epochDrift
              (AyUECRDisj digestMismatch
                (AyUECRDisj reconstructionMismatch fingerprintDrift)))))))

def AyUECRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUECRDisj noClaim originalUnsat

theorem ay_uecr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUECRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uecr_conj_left
    (p : Prop) (q : Prop) :
    AyUECRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uecr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUECRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uecr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUECRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uecr_parent_coverage
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUECRSuffixParents replaySuffix parentCoverage emptyClause ->
    replaySuffix ->
    parentCoverage := by
  intro parents
  exact parents (replaySuffix -> parentCoverage)
    (fun suffix_to_parents _parents_to_empty => suffix_to_parents)

theorem ay_uecr_empty_clause
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) :
    AyUECRSuffixParents replaySuffix parentCoverage emptyClause ->
    parentCoverage ->
    emptyClause := by
  intro parents
  exact parents (parentCoverage -> emptyClause)
    (fun _suffix_to_parents parents_to_empty => parents_to_empty)

theorem ay_uecr_antecedent_retention
    (replaySuffix : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) :
    AyUECRAntecedentRetention replaySuffix antecedentRetention
      retentionAccepted ->
    replaySuffix ->
    antecedentRetention := by
  intro retention
  exact retention (replaySuffix -> antecedentRetention)
    (fun suffix_to_retention _retention_to_accept => suffix_to_retention)

theorem ay_uecr_retention_accepted
    (replaySuffix : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) :
    AyUECRAntecedentRetention replaySuffix antecedentRetention
      retentionAccepted ->
    antecedentRetention ->
    retentionAccepted := by
  intro retention
  exact retention (antecedentRetention -> retentionAccepted)
    (fun _suffix_to_retention retention_to_accept => retention_to_accept)

theorem ay_uecr_checker_transcript
    (replaySuffix : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUECRCheckerTranscript replaySuffix checkerTranscript
      checkerAccepted ->
    replaySuffix ->
    checkerTranscript := by
  intro transcript
  exact transcript (replaySuffix -> checkerTranscript)
    (fun suffix_to_transcript _transcript_to_accept =>
      suffix_to_transcript)

theorem ay_uecr_checker_accepted
    (replaySuffix : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUECRCheckerTranscript replaySuffix checkerTranscript
      checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _suffix_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_uecr_epoch_member
    (replaySuffix : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUECREpochDigest replaySuffix epochMember digestMember
      epochDigestAccepted ->
    replaySuffix ->
    epochMember := by
  intro epoch_digest
  exact epoch_digest (replaySuffix -> epochMember)
    (fun suffix_to_epoch _tail => suffix_to_epoch)

theorem ay_uecr_digest_member
    (replaySuffix : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUECREpochDigest replaySuffix epochMember digestMember
      epochDigestAccepted ->
    epochMember ->
    digestMember := by
  intro epoch_digest
  exact epoch_digest (epochMember -> digestMember)
    (fun _suffix_to_epoch tail =>
      tail (epochMember -> digestMember)
        (fun epoch_to_digest _digest_to_accept => epoch_to_digest))

theorem ay_uecr_epoch_digest_accepted
    (replaySuffix : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop) :
    AyUECREpochDigest replaySuffix epochMember digestMember
      epochDigestAccepted ->
    digestMember ->
    epochDigestAccepted := by
  intro epoch_digest
  exact epoch_digest (digestMember -> epochDigestAccepted)
    (fun _suffix_to_epoch tail =>
      tail (digestMember -> epochDigestAccepted)
        (fun _epoch_to_digest digest_to_accept => digest_to_accept))

theorem ay_uecr_reconstruction_handle
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUECRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    reconstructionHandle := by
  intro reconstruction
  exact ay_uecr_conj_left reconstructionHandle
    (AyUECRConj
      (AyUECRMap emptyClause visibleUnsat)
      (AyUECRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_uecr_visible_unsat_from_empty
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUECRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun _handle tail =>
      tail (emptyClause -> visibleUnsat)
        (fun empty_to_visible _visible_to_original => empty_to_visible))

theorem ay_uecr_original_unsat_from_visible
    (emptyClause : Prop) (reconstructionHandle : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUECRReconstruction emptyClause reconstructionHandle visibleUnsat
      originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _handle tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _empty_to_visible visible_to_original => visible_to_original))

theorem ay_uecr_fingerprint_agrees
    (replaySuffix : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUECRFingerprint replaySuffix fingerprintAgrees visibleUnsat ->
    replaySuffix ->
    fingerprintAgrees := by
  intro fingerprint
  exact fingerprint (replaySuffix -> fingerprintAgrees)
    (fun suffix_to_fingerprint _fingerprint_to_visible =>
      suffix_to_fingerprint)

theorem ay_uecr_visible_unsat_from_fingerprint
    (replaySuffix : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) :
    AyUECRFingerprint replaySuffix fingerprintAgrees visibleUnsat ->
    fingerprintAgrees ->
    visibleUnsat := by
  intro fingerprint
  exact fingerprint (fingerprintAgrees -> visibleUnsat)
    (fun _suffix_to_fingerprint fingerprint_to_visible =>
      fingerprint_to_visible)

theorem ay_uecr_accepted_evidence
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUECRAcceptedSuffix replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUECRAcceptedEvidence replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat := by
  intro accepted
  exact ay_uecr_conj_left
    (AyUECRAcceptedEvidence replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_uecr_accepted_original_unsat
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUECRAcceptedSuffix replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_uecr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUECRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uecr_disj_right noClaim originalUnsat unsat

theorem ay_uecr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUECRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uecr_disj_left noClaim originalUnsat no_claim

theorem ay_uecr_accepted_suffix_publish_sound
    (replaySuffix : Prop) (parentCoverage : Prop)
    (emptyClause : Prop) (antecedentRetention : Prop)
    (retentionAccepted : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (epochMember : Prop)
    (digestMember : Prop) (epochDigestAccepted : Prop)
    (reconstructionHandle : Prop) (fingerprintAgrees : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUECRAcceptedSuffix replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat ->
    AyUECRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_uecr_public_unsat_report noClaim originalUnsat
    (ay_uecr_accepted_original_unsat replaySuffix parentCoverage emptyClause
      antecedentRetention retentionAccepted checkerTranscript checkerAccepted
      epochMember digestMember epochDigestAccepted reconstructionHandle
      fingerprintAgrees visibleUnsat originalUnsat accepted)

theorem ay_uecr_bad_suffix_no_claim
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uecr_conj_left noClaim recompute fail_closed)

theorem ay_uecr_bad_suffix_recompute
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_uecr_bad_suffix_public_no_claim
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute ->
    AyUECRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uecr_public_no_claim_report noClaim originalUnsat
    (ay_uecr_bad_suffix_no_claim missingParentCoverage
      incorrectParentCoverage missingAntecedentRetention checkerRejected
      epochDrift digestMismatch reconstructionMismatch fingerprintDrift
      noClaim recompute bad)

theorem ay_uecr_bad_suffix_cannot_publish
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_uecr_bad_suffix_no_claim missingParentCoverage
      incorrectParentCoverage missingAntecedentRetention checkerRejected
      epochDrift digestMismatch reconstructionMismatch fingerprintDrift
      noClaim recompute bad)
    unsat

theorem ay_uecr_missing_parent_coverage_no_claim
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingParentCoverage ->
    AyUECRConj noClaim recompute ->
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute := by
  intro missing_parent
  intro fail_closed
  exact ay_uecr_conj_intro
    (AyUECRConj noClaim recompute)
    (AyUECRDisj missingParentCoverage
      (AyUECRDisj incorrectParentCoverage
        (AyUECRDisj missingAntecedentRetention
          (AyUECRDisj checkerRejected
            (AyUECRDisj epochDrift
              (AyUECRDisj digestMismatch
                (AyUECRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_uecr_disj_left missingParentCoverage
      (AyUECRDisj incorrectParentCoverage
        (AyUECRDisj missingAntecedentRetention
          (AyUECRDisj checkerRejected
            (AyUECRDisj epochDrift
              (AyUECRDisj digestMismatch
                (AyUECRDisj reconstructionMismatch fingerprintDrift))))))
      missing_parent)

theorem ay_uecr_incorrect_parent_coverage_no_claim
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) :
    incorrectParentCoverage ->
    AyUECRConj noClaim recompute ->
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute := by
  intro incorrect_parent
  intro fail_closed
  exact ay_uecr_conj_intro
    (AyUECRConj noClaim recompute)
    (AyUECRDisj missingParentCoverage
      (AyUECRDisj incorrectParentCoverage
        (AyUECRDisj missingAntecedentRetention
          (AyUECRDisj checkerRejected
            (AyUECRDisj epochDrift
              (AyUECRDisj digestMismatch
                (AyUECRDisj reconstructionMismatch fingerprintDrift)))))))
    fail_closed
    (ay_uecr_disj_right missingParentCoverage
      (AyUECRDisj incorrectParentCoverage
        (AyUECRDisj missingAntecedentRetention
          (AyUECRDisj checkerRejected
            (AyUECRDisj epochDrift
              (AyUECRDisj digestMismatch
                (AyUECRDisj reconstructionMismatch fingerprintDrift))))))
      (ay_uecr_disj_left incorrectParentCoverage
        (AyUECRDisj missingAntecedentRetention
          (AyUECRDisj checkerRejected
            (AyUECRDisj epochDrift
              (AyUECRDisj digestMismatch
                (AyUECRDisj reconstructionMismatch fingerprintDrift)))))
        incorrect_parent))

theorem ay_uecr_parent_coverage_failure_cannot_publish
    (missingParentCoverage : Prop) (incorrectParentCoverage : Prop)
    (missingAntecedentRetention : Prop) (checkerRejected : Prop)
    (epochDrift : Prop) (digestMismatch : Prop)
    (reconstructionMismatch : Prop) (fingerprintDrift : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUECRBadSuffix missingParentCoverage incorrectParentCoverage
      missingAntecedentRetention checkerRejected epochDrift digestMismatch
      reconstructionMismatch fingerprintDrift noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_uecr_bad_suffix_cannot_publish missingParentCoverage
    incorrectParentCoverage missingAntecedentRetention checkerRejected
    epochDrift digestMismatch reconstructionMismatch fingerprintDrift
    noClaim recompute originalUnsat bad
