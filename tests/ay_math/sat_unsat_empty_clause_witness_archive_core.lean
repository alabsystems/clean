-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded empty-clause witness archive soundness for ay. Propositions stand
-- for archived empty-clause witnesses, archive membership, dependency
-- coverage, proof-fragment digest chains, original reconstruction, checker
-- replay, exit-code contracts, and fail-closed no-claim/recompute diagnostics.

def AyUEWAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUEWADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUEWAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUEWAArchiveMembership
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :=
  AyUEWAConj emptyWitness
    (AyUEWAConj
      (AyUEWAMap emptyWitness archiveMember)
      (AyUEWAMap archiveMember archiveAccepted))

def AyUEWADependencyCoverage
    (emptyWitness : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUEWAConj
    (AyUEWAMap emptyWitness dependencyCoverage)
    (AyUEWAMap dependencyCoverage emptyClause)

def AyUEWADigestChain
    (emptyWitness : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) :=
  AyUEWAConj
    (AyUEWAMap emptyWitness fragmentDigestChain)
    (AyUEWAMap fragmentDigestChain digestAccepted)

def AyUEWAReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUEWAConj
    (AyUEWAMap emptyClause visibleUnsat)
    (AyUEWAMap visibleUnsat originalUnsat)

def AyUEWACheckerReplay
    (emptyWitness : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUEWAConj
    (AyUEWAMap emptyWitness checkerReplay)
    (AyUEWAMap checkerReplay replayAccepted)

def AyUEWAExitCodeContract
    (originalUnsat : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :=
  AyUEWAConj
    (AyUEWAMap originalUnsat unsatExitCode)
    (AyUEWAMap unsatExitCode publicUnsatAnswer)

def AyUEWAAcceptedArchive
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :=
  AyUEWAConj
    (AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted)
    (AyUEWAConj
      (AyUEWADependencyCoverage emptyWitness dependencyCoverage
        emptyClause)
      (AyUEWAConj
        (AyUEWADigestChain emptyWitness fragmentDigestChain
          digestAccepted)
        (AyUEWAConj
          (AyUEWAReconstruction emptyClause visibleUnsat originalUnsat)
          (AyUEWAConj
            (AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted)
            (AyUEWAExitCodeContract originalUnsat unsatExitCode
              publicUnsatAnswer)))))

def AyUEWABadArchive
    (missingWitness : Prop) (staleArchiveDigest : Prop)
    (uncoveredDependency : Prop) (reconstructionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUEWAConj
    (AyUEWAConj noClaim recompute)
    (AyUEWADisj missingWitness
      (AyUEWADisj staleArchiveDigest
        (AyUEWADisj uncoveredDependency
          (AyUEWADisj reconstructionMismatch replayRejected))))

def AyUEWAPublicReport (noClaim : Prop) (publicUnsatAnswer : Prop) :=
  AyUEWADisj noClaim publicUnsatAnswer

theorem ay_uewa_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUEWAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uewa_conj_left
    (p : Prop) (q : Prop) :
    AyUEWAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uewa_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUEWADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uewa_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUEWADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uewa_empty_witness
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :
    AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted ->
    emptyWitness := by
  intro archive
  exact ay_uewa_conj_left emptyWitness
    (AyUEWAConj
      (AyUEWAMap emptyWitness archiveMember)
      (AyUEWAMap archiveMember archiveAccepted))
    archive

theorem ay_uewa_archive_member
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :
    AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted ->
    archiveMember := by
  intro archive
  exact archive archiveMember
    (fun witness tail =>
      tail archiveMember
        (fun witness_to_member _member_to_accept =>
          witness_to_member witness))

theorem ay_uewa_archive_accepted
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :
    AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted ->
    archiveAccepted := by
  intro archive
  exact archive archiveAccepted
    (fun witness tail =>
      tail archiveAccepted
        (fun witness_to_member member_to_accept =>
          member_to_accept (witness_to_member witness)))

theorem ay_uewa_dependency_coverage
    (emptyWitness : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUEWADependencyCoverage emptyWitness dependencyCoverage emptyClause ->
    emptyWitness ->
    dependencyCoverage := by
  intro coverage
  exact coverage (emptyWitness -> dependencyCoverage)
    (fun witness_to_coverage _coverage_to_empty => witness_to_coverage)

theorem ay_uewa_empty_clause
    (emptyWitness : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUEWADependencyCoverage emptyWitness dependencyCoverage emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _witness_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_uewa_digest_chain
    (emptyWitness : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) :
    AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted ->
    emptyWitness ->
    fragmentDigestChain := by
  intro chain
  exact chain (emptyWitness -> fragmentDigestChain)
    (fun witness_to_chain _chain_to_accept => witness_to_chain)

theorem ay_uewa_digest_accepted
    (emptyWitness : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) :
    AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted ->
    fragmentDigestChain ->
    digestAccepted := by
  intro chain
  exact chain (fragmentDigestChain -> digestAccepted)
    (fun _witness_to_chain chain_to_accept => chain_to_accept)

theorem ay_uewa_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUEWAReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uewa_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUEWAReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uewa_replay_transcript
    (emptyWitness : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted ->
    emptyWitness ->
    checkerReplay := by
  intro replay
  exact replay (emptyWitness -> checkerReplay)
    (fun witness_to_replay _replay_to_accept => witness_to_replay)

theorem ay_uewa_replay_accepted
    (emptyWitness : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _witness_to_replay replay_to_accept => replay_to_accept)

theorem ay_uewa_unsat_exit_code
    (originalUnsat : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAExitCodeContract originalUnsat unsatExitCode
      publicUnsatAnswer ->
    originalUnsat ->
    unsatExitCode := by
  intro contract
  exact contract (originalUnsat -> unsatExitCode)
    (fun original_to_exit _exit_to_public => original_to_exit)

theorem ay_uewa_public_unsat_answer
    (originalUnsat : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAExitCodeContract originalUnsat unsatExitCode
      publicUnsatAnswer ->
    unsatExitCode ->
    publicUnsatAnswer := by
  intro contract
  exact contract (unsatExitCode -> publicUnsatAnswer)
    (fun _original_to_exit exit_to_public => exit_to_public)

theorem ay_uewa_archive_membership
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted := by
  intro accepted
  exact ay_uewa_conj_left
    (AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted)
    (AyUEWAConj
      (AyUEWADependencyCoverage emptyWitness dependencyCoverage
        emptyClause)
      (AyUEWAConj
        (AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted)
        (AyUEWAConj
          (AyUEWAReconstruction emptyClause visibleUnsat originalUnsat)
          (AyUEWAConj
            (AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted)
            (AyUEWAExitCodeContract originalUnsat unsatExitCode
              publicUnsatAnswer)))))
    accepted

theorem ay_uewa_archive_coverage
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWADependencyCoverage emptyWitness dependencyCoverage emptyClause := by
  intro accepted
  exact accepted
    (AyUEWADependencyCoverage emptyWitness dependencyCoverage emptyClause)
    (fun _membership tail =>
      tail (AyUEWADependencyCoverage emptyWitness dependencyCoverage
        emptyClause)
        (fun coverage _rest => coverage))

theorem ay_uewa_archive_digest_chain
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted := by
  intro accepted
  exact accepted
    (AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted)
    (fun _membership tail =>
      tail (AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted)
        (fun _coverage rest =>
          rest (AyUEWADigestChain emptyWitness fragmentDigestChain
            digestAccepted)
            (fun chain _tail => chain)))

theorem ay_uewa_archive_reconstruction
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWAReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUEWAReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _membership tail =>
      tail (AyUEWAReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _coverage rest =>
          rest (AyUEWAReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _chain tail2 =>
              tail2 (AyUEWAReconstruction emptyClause visibleUnsat
                originalUnsat)
                (fun reconstruction _tail => reconstruction))))

theorem ay_uewa_archive_replay
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted := by
  intro accepted
  exact accepted (AyUEWACheckerReplay emptyWitness checkerReplay
    replayAccepted)
    (fun _membership tail =>
      tail (AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted)
        (fun _coverage rest =>
          rest (AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted)
            (fun _chain tail2 =>
              tail2 (AyUEWACheckerReplay emptyWitness checkerReplay
                replayAccepted)
                (fun _reconstruction tail3 =>
                  tail3 (AyUEWACheckerReplay emptyWitness checkerReplay
                    replayAccepted)
                    (fun replay _contract => replay)))))

theorem ay_uewa_archive_exit_contract
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWAExitCodeContract originalUnsat unsatExitCode
      publicUnsatAnswer := by
  intro accepted
  exact accepted
    (AyUEWAExitCodeContract originalUnsat unsatExitCode publicUnsatAnswer)
    (fun _membership tail =>
      tail
        (AyUEWAExitCodeContract originalUnsat unsatExitCode
          publicUnsatAnswer)
        (fun _coverage rest =>
          rest
            (AyUEWAExitCodeContract originalUnsat unsatExitCode
              publicUnsatAnswer)
            (fun _chain tail2 =>
              tail2
                (AyUEWAExitCodeContract originalUnsat unsatExitCode
                  publicUnsatAnswer)
                (fun _reconstruction tail3 =>
                  tail3
                    (AyUEWAExitCodeContract originalUnsat unsatExitCode
                      publicUnsatAnswer)
                    (fun _replay contract => contract)))))

theorem ay_uewa_accepted_empty_clause
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    emptyClause := by
  intro accepted
  have membership :
      AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted :=
    ay_uewa_archive_membership emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have coverage :
      AyUEWADependencyCoverage emptyWitness dependencyCoverage
        emptyClause :=
    ay_uewa_archive_coverage emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have witness : emptyWitness :=
    ay_uewa_empty_witness emptyWitness archiveMember archiveAccepted
      membership
  have covered : dependencyCoverage :=
    ay_uewa_dependency_coverage emptyWitness dependencyCoverage
      emptyClause coverage witness
  exact ay_uewa_empty_clause emptyWitness dependencyCoverage emptyClause
    coverage covered

theorem ay_uewa_accepted_digest
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    digestAccepted := by
  intro accepted
  have membership :
      AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted :=
    ay_uewa_archive_membership emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have chain :
      AyUEWADigestChain emptyWitness fragmentDigestChain digestAccepted :=
    ay_uewa_archive_digest_chain emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have witness : emptyWitness :=
    ay_uewa_empty_witness emptyWitness archiveMember archiveAccepted
      membership
  have digest_chain : fragmentDigestChain :=
    ay_uewa_digest_chain emptyWitness fragmentDigestChain digestAccepted
      chain witness
  exact ay_uewa_digest_accepted emptyWitness fragmentDigestChain
    digestAccepted chain digest_chain

theorem ay_uewa_accepted_replay
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    replayAccepted := by
  intro accepted
  have membership :
      AyUEWAArchiveMembership emptyWitness archiveMember archiveAccepted :=
    ay_uewa_archive_membership emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have replay :
      AyUEWACheckerReplay emptyWitness checkerReplay replayAccepted :=
    ay_uewa_archive_replay emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have witness : emptyWitness :=
    ay_uewa_empty_witness emptyWitness archiveMember archiveAccepted
      membership
  have transcript : checkerReplay :=
    ay_uewa_replay_transcript emptyWitness checkerReplay replayAccepted
      replay witness
  exact ay_uewa_replay_accepted emptyWitness checkerReplay replayAccepted
    replay transcript

theorem ay_uewa_accepted_original_unsat
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_uewa_accepted_empty_clause emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have reconstruction :
      AyUEWAReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_uewa_archive_reconstruction emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have visible : visibleUnsat :=
    ay_uewa_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_uewa_original_unsat emptyClause visibleUnsat originalUnsat
    reconstruction visible

theorem ay_uewa_accepted_public_unsat_answer
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    publicUnsatAnswer := by
  intro accepted
  have original : originalUnsat :=
    ay_uewa_accepted_original_unsat emptyWitness archiveMember
      archiveAccepted dependencyCoverage emptyClause fragmentDigestChain
      digestAccepted visibleUnsat originalUnsat checkerReplay replayAccepted
      unsatExitCode publicUnsatAnswer accepted
  have contract :
      AyUEWAExitCodeContract originalUnsat unsatExitCode
        publicUnsatAnswer :=
    ay_uewa_archive_exit_contract emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer accepted
  have exit_code : unsatExitCode :=
    ay_uewa_unsat_exit_code originalUnsat unsatExitCode
      publicUnsatAnswer contract original
  exact ay_uewa_public_unsat_answer originalUnsat unsatExitCode
    publicUnsatAnswer contract exit_code

theorem ay_uewa_public_unsat_report
    (noClaim : Prop) (publicUnsatAnswer : Prop) :
    publicUnsatAnswer -> AyUEWAPublicReport noClaim publicUnsatAnswer := by
  intro answer
  exact ay_uewa_disj_right noClaim publicUnsatAnswer answer

theorem ay_uewa_public_no_claim_report
    (noClaim : Prop) (publicUnsatAnswer : Prop) :
    noClaim -> AyUEWAPublicReport noClaim publicUnsatAnswer := by
  intro no_claim
  exact ay_uewa_disj_left noClaim publicUnsatAnswer no_claim

theorem ay_uewa_accepted_archive_publish_sound
    (emptyWitness : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (fragmentDigestChain : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) (unsatExitCode : Prop)
    (publicUnsatAnswer : Prop) (noClaim : Prop) :
    AyUEWAAcceptedArchive emptyWitness archiveMember archiveAccepted
      dependencyCoverage emptyClause fragmentDigestChain digestAccepted
      visibleUnsat originalUnsat checkerReplay replayAccepted unsatExitCode
      publicUnsatAnswer ->
    AyUEWAPublicReport noClaim publicUnsatAnswer := by
  intro accepted
  exact ay_uewa_public_unsat_report noClaim publicUnsatAnswer
    (ay_uewa_accepted_public_unsat_answer emptyWitness archiveMember
      archiveAccepted dependencyCoverage emptyClause fragmentDigestChain
      digestAccepted visibleUnsat originalUnsat checkerReplay replayAccepted
      unsatExitCode publicUnsatAnswer accepted)

theorem ay_uewa_bad_archive_no_claim
    (missingWitness : Prop) (staleArchiveDigest : Prop)
    (uncoveredDependency : Prop) (reconstructionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWABadArchive missingWitness staleArchiveDigest uncoveredDependency
      reconstructionMismatch replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_uewa_bad_archive_recompute
    (missingWitness : Prop) (staleArchiveDigest : Prop)
    (uncoveredDependency : Prop) (reconstructionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWABadArchive missingWitness staleArchiveDigest uncoveredDependency
      reconstructionMismatch replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_uewa_bad_archive_public_no_claim
    (missingWitness : Prop) (staleArchiveDigest : Prop)
    (uncoveredDependency : Prop) (reconstructionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (publicUnsatAnswer : Prop) :
    AyUEWABadArchive missingWitness staleArchiveDigest uncoveredDependency
      reconstructionMismatch replayRejected noClaim recompute ->
    AyUEWAPublicReport noClaim publicUnsatAnswer := by
  intro bad
  exact ay_uewa_public_no_claim_report noClaim publicUnsatAnswer
    (ay_uewa_bad_archive_no_claim missingWitness staleArchiveDigest
      uncoveredDependency reconstructionMismatch replayRejected noClaim
      recompute bad)

theorem ay_uewa_bad_archive_cannot_publish
    (missingWitness : Prop) (staleArchiveDigest : Prop)
    (uncoveredDependency : Prop) (reconstructionMismatch : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUEWABadArchive missingWitness staleArchiveDigest uncoveredDependency
      reconstructionMismatch replayRejected noClaim recompute ->
    AyUEWAConj noClaim recompute := by
  intro bad
  exact bad (AyUEWAConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

