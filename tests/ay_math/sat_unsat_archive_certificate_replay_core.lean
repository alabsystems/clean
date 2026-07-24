-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded archived UNSAT certificate replay soundness for ay. Propositions
-- stand for archive membership, digest roots, dependency coverage,
-- empty-clause witnesses, checker replay transcripts, original reconstruction,
-- and no-claim/recompute diagnostics for stale archives, missing dependencies,
-- replay rejection, or reconstruction mismatch.

def AyUACRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUACRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUACRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUACRArchiveMembership
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) :=
  AyUACRConj archiveEntry
    (AyUACRConj
      (AyUACRMap archiveEntry membershipProof)
      (AyUACRMap membershipProof archivedCertificate))

def AyUACRDigestRoot
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :=
  AyUACRConj
    (AyUACRMap archivedCertificate digestRoot)
    (AyUACRMap digestRoot rootAccepted)

def AyUACRDependencyCoverage
    (archivedCertificate : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUACRConj
    (AyUACRMap archivedCertificate dependencyCoverage)
    (AyUACRMap dependencyCoverage emptyClause)

def AyUACRReplayTranscript
    (archivedCertificate : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) :=
  AyUACRConj
    (AyUACRMap archivedCertificate replayTranscript)
    (AyUACRMap replayTranscript replayAccepted)

def AyUACRReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUACRConj
    (AyUACRMap emptyClause visibleUnsat)
    (AyUACRMap visibleUnsat originalUnsat)

def AyUACRAcceptedReplay
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUACRConj
    (AyUACRArchiveMembership archiveEntry membershipProof
      archivedCertificate)
    (AyUACRConj
      (AyUACRDigestRoot archivedCertificate digestRoot rootAccepted)
      (AyUACRConj
        (AyUACRDependencyCoverage archivedCertificate dependencyCoverage
          emptyClause)
        (AyUACRConj
          (AyUACRReplayTranscript archivedCertificate replayTranscript
            replayAccepted)
          (AyUACRReconstruction emptyClause visibleUnsat originalUnsat))))

def AyUACRBadReplay
    (staleArchiveEntry : Prop) (missingDependencies : Prop)
    (replayRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUACRConj
    (AyUACRConj noClaim recompute)
    (AyUACRDisj staleArchiveEntry
      (AyUACRDisj missingDependencies
        (AyUACRDisj replayRejected reconstructionMismatch)))

def AyUACRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUACRDisj noClaim originalUnsat

theorem ay_uacr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUACRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uacr_conj_left
    (p : Prop) (q : Prop) :
    AyUACRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uacr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUACRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uacr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUACRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uacr_archive_entry
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) :
    AyUACRArchiveMembership archiveEntry membershipProof
      archivedCertificate ->
    archiveEntry := by
  intro membership
  exact ay_uacr_conj_left archiveEntry
    (AyUACRConj
      (AyUACRMap archiveEntry membershipProof)
      (AyUACRMap membershipProof archivedCertificate))
    membership

theorem ay_uacr_membership_proof
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) :
    AyUACRArchiveMembership archiveEntry membershipProof
      archivedCertificate ->
    membershipProof := by
  intro membership
  exact membership membershipProof
    (fun entry tail =>
      tail membershipProof
        (fun entry_to_membership _membership_to_archive =>
          entry_to_membership entry))

theorem ay_uacr_archived_certificate
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) :
    AyUACRArchiveMembership archiveEntry membershipProof
      archivedCertificate ->
    archivedCertificate := by
  intro membership
  exact membership archivedCertificate
    (fun entry tail =>
      tail archivedCertificate
        (fun entry_to_membership membership_to_archive =>
          membership_to_archive (entry_to_membership entry)))

theorem ay_uacr_digest_root_value
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :
    AyUACRDigestRoot archivedCertificate digestRoot rootAccepted ->
    archivedCertificate ->
    digestRoot := by
  intro root
  exact root (archivedCertificate -> digestRoot)
    (fun certificate_to_root _root_to_accept => certificate_to_root)

theorem ay_uacr_root_accepted
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :
    AyUACRDigestRoot archivedCertificate digestRoot rootAccepted ->
    digestRoot ->
    rootAccepted := by
  intro root
  exact root (digestRoot -> rootAccepted)
    (fun _certificate_to_root root_to_accept => root_to_accept)

theorem ay_uacr_dependency_coverage
    (archivedCertificate : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUACRDependencyCoverage archivedCertificate dependencyCoverage
      emptyClause ->
    archivedCertificate ->
    dependencyCoverage := by
  intro coverage
  exact coverage (archivedCertificate -> dependencyCoverage)
    (fun certificate_to_coverage _coverage_to_empty =>
      certificate_to_coverage)

theorem ay_uacr_dependency_empty_clause
    (archivedCertificate : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUACRDependencyCoverage archivedCertificate dependencyCoverage
      emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _certificate_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_uacr_replay_transcript_value
    (archivedCertificate : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) :
    AyUACRReplayTranscript archivedCertificate replayTranscript
      replayAccepted ->
    archivedCertificate ->
    replayTranscript := by
  intro replay
  exact replay (archivedCertificate -> replayTranscript)
    (fun certificate_to_transcript _transcript_to_accept =>
      certificate_to_transcript)

theorem ay_uacr_replay_accepted
    (archivedCertificate : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) :
    AyUACRReplayTranscript archivedCertificate replayTranscript
      replayAccepted ->
    replayTranscript ->
    replayAccepted := by
  intro replay
  exact replay (replayTranscript -> replayAccepted)
    (fun _certificate_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_uacr_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uacr_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uacr_replay_membership
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    AyUACRArchiveMembership archiveEntry membershipProof
      archivedCertificate := by
  intro proof
  exact ay_uacr_conj_left
    (AyUACRArchiveMembership archiveEntry membershipProof
      archivedCertificate)
    (AyUACRConj
      (AyUACRDigestRoot archivedCertificate digestRoot rootAccepted)
      (AyUACRConj
        (AyUACRDependencyCoverage archivedCertificate dependencyCoverage
          emptyClause)
        (AyUACRConj
          (AyUACRReplayTranscript archivedCertificate replayTranscript
            replayAccepted)
          (AyUACRReconstruction emptyClause visibleUnsat originalUnsat))))
    proof

theorem ay_uacr_replay_digest_root
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    AyUACRDigestRoot archivedCertificate digestRoot rootAccepted := by
  intro proof
  exact proof (AyUACRDigestRoot archivedCertificate digestRoot rootAccepted)
    (fun _membership tail =>
      tail (AyUACRDigestRoot archivedCertificate digestRoot rootAccepted)
        (fun root _rest => root))

theorem ay_uacr_replay_coverage
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    AyUACRDependencyCoverage archivedCertificate dependencyCoverage
      emptyClause := by
  intro proof
  exact proof
    (AyUACRDependencyCoverage archivedCertificate dependencyCoverage
      emptyClause)
    (fun _membership tail =>
      tail
        (AyUACRDependencyCoverage archivedCertificate dependencyCoverage
          emptyClause)
        (fun _root rest =>
          rest
            (AyUACRDependencyCoverage archivedCertificate dependencyCoverage
              emptyClause)
            (fun coverage _tail => coverage)))

theorem ay_uacr_replay_transcript
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    AyUACRReplayTranscript archivedCertificate replayTranscript
      replayAccepted := by
  intro proof
  exact proof
    (AyUACRReplayTranscript archivedCertificate replayTranscript
      replayAccepted)
    (fun _membership tail =>
      tail
        (AyUACRReplayTranscript archivedCertificate replayTranscript
          replayAccepted)
        (fun _root rest =>
          rest
            (AyUACRReplayTranscript archivedCertificate replayTranscript
              replayAccepted)
            (fun _coverage tail2 =>
              tail2
                (AyUACRReplayTranscript archivedCertificate replayTranscript
                  replayAccepted)
                (fun transcript _reconstruction => transcript))))

theorem ay_uacr_replay_reconstruction
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    AyUACRReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUACRReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _membership tail =>
      tail (AyUACRReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _root rest =>
          rest (AyUACRReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage tail2 =>
              tail2
                (AyUACRReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _transcript reconstruction => reconstruction))))

theorem ay_uacr_replay_root_accepted
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    rootAccepted := by
  intro proof
  have membership :
      AyUACRArchiveMembership archiveEntry membershipProof
        archivedCertificate :=
    ay_uacr_replay_membership archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have root :
      AyUACRDigestRoot archivedCertificate digestRoot rootAccepted :=
    ay_uacr_replay_digest_root archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have archived : archivedCertificate :=
    ay_uacr_archived_certificate archiveEntry membershipProof
      archivedCertificate membership
  have digest : digestRoot :=
    ay_uacr_digest_root_value archivedCertificate digestRoot rootAccepted
      root archived
  exact ay_uacr_root_accepted archivedCertificate digestRoot rootAccepted
    root digest

theorem ay_uacr_replay_checker_accepted
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    replayAccepted := by
  intro proof
  have membership :
      AyUACRArchiveMembership archiveEntry membershipProof
        archivedCertificate :=
    ay_uacr_replay_membership archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have transcript_proof :
      AyUACRReplayTranscript archivedCertificate replayTranscript
        replayAccepted :=
    ay_uacr_replay_transcript archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have archived : archivedCertificate :=
    ay_uacr_archived_certificate archiveEntry membershipProof
      archivedCertificate membership
  have transcript : replayTranscript :=
    ay_uacr_replay_transcript_value archivedCertificate replayTranscript
      replayAccepted transcript_proof archived
  exact ay_uacr_replay_accepted archivedCertificate replayTranscript
    replayAccepted transcript_proof transcript

theorem ay_uacr_replay_empty_clause
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    emptyClause := by
  intro proof
  have membership :
      AyUACRArchiveMembership archiveEntry membershipProof
        archivedCertificate :=
    ay_uacr_replay_membership archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have coverage :
      AyUACRDependencyCoverage archivedCertificate dependencyCoverage
        emptyClause :=
    ay_uacr_replay_coverage archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat proof
  have archived : archivedCertificate :=
    ay_uacr_archived_certificate archiveEntry membershipProof
      archivedCertificate membership
  have covered : dependencyCoverage :=
    ay_uacr_dependency_coverage archivedCertificate dependencyCoverage
      emptyClause coverage archived
  exact ay_uacr_dependency_empty_clause archivedCertificate
    dependencyCoverage emptyClause coverage covered

theorem ay_uacr_accepted_replay_original_unsat
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  have empty : emptyClause :=
    ay_uacr_replay_empty_clause archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have reconstruction :
      AyUACRReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_uacr_replay_reconstruction archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof
  have visible : visibleUnsat :=
    ay_uacr_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_uacr_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_uacr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUACRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uacr_disj_right noClaim originalUnsat unsat

theorem ay_uacr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUACRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uacr_disj_left noClaim originalUnsat no_claim

theorem ay_uacr_accepted_replay_publish_sound
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedCertificate : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (replayTranscript : Prop)
    (replayAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUACRAcceptedReplay archiveEntry membershipProof archivedCertificate
      digestRoot rootAccepted dependencyCoverage emptyClause replayTranscript
      replayAccepted visibleUnsat originalUnsat ->
    AyUACRPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_uacr_public_unsat_report noClaim originalUnsat
    (ay_uacr_accepted_replay_original_unsat archiveEntry membershipProof
      archivedCertificate digestRoot rootAccepted dependencyCoverage
      emptyClause replayTranscript replayAccepted visibleUnsat originalUnsat
      proof)

theorem ay_uacr_bad_replay_no_claim
    (staleArchiveEntry : Prop) (missingDependencies : Prop)
    (replayRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUACRBadReplay staleArchiveEntry missingDependencies replayRejected
      reconstructionMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uacr_bad_replay_recompute
    (staleArchiveEntry : Prop) (missingDependencies : Prop)
    (replayRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUACRBadReplay staleArchiveEntry missingDependencies replayRejected
      reconstructionMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uacr_bad_replay_public_no_claim
    (staleArchiveEntry : Prop) (missingDependencies : Prop)
    (replayRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (originalUnsat : Prop) (recompute : Prop) :
    AyUACRBadReplay staleArchiveEntry missingDependencies replayRejected
      reconstructionMismatch noClaim recompute ->
    AyUACRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uacr_public_no_claim_report noClaim originalUnsat
    (ay_uacr_bad_replay_no_claim staleArchiveEntry missingDependencies
      replayRejected reconstructionMismatch noClaim recompute bad)

theorem ay_uacr_bad_replay_cannot_publish_unsat
    (staleArchiveEntry : Prop) (missingDependencies : Prop)
    (replayRejected : Prop) (reconstructionMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUACRBadReplay staleArchiveEntry missingDependencies replayRejected
      reconstructionMismatch noClaim recompute ->
    AyUACRConj noClaim recompute := by
  intro bad
  exact bad (AyUACRConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

