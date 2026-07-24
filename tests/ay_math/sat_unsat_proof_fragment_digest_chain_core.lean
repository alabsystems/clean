-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof-fragment digest-chain soundness for ay. Propositions
-- stand for chained fragment digests, archive membership, assumption/cube frame
-- lineage, dependency coverage, checker replay, original UNSAT reconstruction,
-- and fail-closed no-claim/recompute diagnostics.

def AyUPFDConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPFDDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPFDMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPFDDigestChain
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) :=
  AyUPFDConj fragmentDigest
    (AyUPFDConj
      (AyUPFDMap fragmentDigest digestLinks)
      (AyUPFDMap digestLinks chainedFragments))

def AyUPFDArchiveMembership
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :=
  AyUPFDConj
    (AyUPFDMap chainedFragments archiveMember)
    (AyUPFDMap archiveMember archiveAccepted)

def AyUPFDFrameLineage
    (frame : Prop) (frameFresh : Prop)
    (chainedFragments : Prop) :=
  AyUPFDConj frame
    (AyUPFDConj
      (AyUPFDMap frame frameFresh)
      (AyUPFDMap frameFresh chainedFragments))

def AyUPFDDependencyCoverage
    (chainedFragments : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUPFDConj
    (AyUPFDMap chainedFragments dependencyCoverage)
    (AyUPFDMap dependencyCoverage emptyClause)

def AyUPFDCheckerReplay
    (chainedFragments : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :=
  AyUPFDConj
    (AyUPFDMap chainedFragments checkerReplay)
    (AyUPFDMap checkerReplay replayAccepted)

def AyUPFDReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPFDConj
    (AyUPFDMap emptyClause visibleUnsat)
    (AyUPFDMap visibleUnsat originalUnsat)

def AyUPFDAcceptedChain
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPFDConj
    (AyUPFDDigestChain fragmentDigest digestLinks chainedFragments)
    (AyUPFDConj
      (AyUPFDArchiveMembership chainedFragments archiveMember
        archiveAccepted)
      (AyUPFDConj
        (AyUPFDFrameLineage frame frameFresh chainedFragments)
        (AyUPFDConj
          (AyUPFDDependencyCoverage chainedFragments dependencyCoverage
            emptyClause)
          (AyUPFDConj
            (AyUPFDCheckerReplay chainedFragments checkerReplay
              replayAccepted)
            (AyUPFDReconstruction emptyClause visibleUnsat
              originalUnsat)))))

def AyUPFDBadChain
    (brokenDigestLink : Prop) (missingFragment : Prop)
    (uncoveredDependency : Prop) (staleFrame : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUPFDConj
    (AyUPFDConj noClaim recompute)
    (AyUPFDDisj brokenDigestLink
      (AyUPFDDisj missingFragment
        (AyUPFDDisj uncoveredDependency
          (AyUPFDDisj staleFrame replayRejected))))

def AyUPFDPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPFDDisj noClaim originalUnsat

theorem ay_upfd_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPFDConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upfd_conj_left
    (p : Prop) (q : Prop) :
    AyUPFDConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upfd_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPFDDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upfd_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPFDDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upfd_fragment_digest
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) :
    AyUPFDDigestChain fragmentDigest digestLinks chainedFragments ->
    fragmentDigest := by
  intro chain
  exact ay_upfd_conj_left fragmentDigest
    (AyUPFDConj
      (AyUPFDMap fragmentDigest digestLinks)
      (AyUPFDMap digestLinks chainedFragments))
    chain

theorem ay_upfd_digest_links
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) :
    AyUPFDDigestChain fragmentDigest digestLinks chainedFragments ->
    digestLinks := by
  intro chain
  exact chain digestLinks
    (fun digest tail =>
      tail digestLinks
        (fun digest_to_links _links_to_fragments =>
          digest_to_links digest))

theorem ay_upfd_chained_fragments_from_digest
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) :
    AyUPFDDigestChain fragmentDigest digestLinks chainedFragments ->
    chainedFragments := by
  intro chain
  exact chain chainedFragments
    (fun digest tail =>
      tail chainedFragments
        (fun digest_to_links links_to_fragments =>
          links_to_fragments (digest_to_links digest)))

theorem ay_upfd_archive_member
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :
    AyUPFDArchiveMembership chainedFragments archiveMember
      archiveAccepted ->
    chainedFragments ->
    archiveMember := by
  intro archive
  exact archive (chainedFragments -> archiveMember)
    (fun fragments_to_member _member_to_accept => fragments_to_member)

theorem ay_upfd_archive_accepted
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) :
    AyUPFDArchiveMembership chainedFragments archiveMember
      archiveAccepted ->
    archiveMember ->
    archiveAccepted := by
  intro archive
  exact archive (archiveMember -> archiveAccepted)
    (fun _fragments_to_member member_to_accept => member_to_accept)

theorem ay_upfd_frame
    (frame : Prop) (frameFresh : Prop) (chainedFragments : Prop) :
    AyUPFDFrameLineage frame frameFresh chainedFragments ->
    frame := by
  intro lineage
  exact ay_upfd_conj_left frame
    (AyUPFDConj
      (AyUPFDMap frame frameFresh)
      (AyUPFDMap frameFresh chainedFragments))
    lineage

theorem ay_upfd_frame_fresh
    (frame : Prop) (frameFresh : Prop) (chainedFragments : Prop) :
    AyUPFDFrameLineage frame frameFresh chainedFragments ->
    frameFresh := by
  intro lineage
  exact lineage frameFresh
    (fun frame_ok tail =>
      tail frameFresh
        (fun frame_to_fresh _fresh_to_fragments =>
          frame_to_fresh frame_ok))

theorem ay_upfd_chained_fragments_from_frame
    (frame : Prop) (frameFresh : Prop) (chainedFragments : Prop) :
    AyUPFDFrameLineage frame frameFresh chainedFragments ->
    chainedFragments := by
  intro lineage
  exact lineage chainedFragments
    (fun frame_ok tail =>
      tail chainedFragments
        (fun frame_to_fresh fresh_to_fragments =>
          fresh_to_fragments (frame_to_fresh frame_ok)))

theorem ay_upfd_dependency_coverage
    (chainedFragments : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUPFDDependencyCoverage chainedFragments dependencyCoverage
      emptyClause ->
    chainedFragments ->
    dependencyCoverage := by
  intro coverage
  exact coverage (chainedFragments -> dependencyCoverage)
    (fun fragments_to_coverage _coverage_to_empty => fragments_to_coverage)

theorem ay_upfd_empty_clause
    (chainedFragments : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUPFDDependencyCoverage chainedFragments dependencyCoverage
      emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _fragments_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_upfd_replay_transcript
    (chainedFragments : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUPFDCheckerReplay chainedFragments checkerReplay replayAccepted ->
    chainedFragments ->
    checkerReplay := by
  intro replay
  exact replay (chainedFragments -> checkerReplay)
    (fun fragments_to_replay _replay_to_accept => fragments_to_replay)

theorem ay_upfd_replay_accepted
    (chainedFragments : Prop) (checkerReplay : Prop)
    (replayAccepted : Prop) :
    AyUPFDCheckerReplay chainedFragments checkerReplay replayAccepted ->
    checkerReplay ->
    replayAccepted := by
  intro replay
  exact replay (checkerReplay -> replayAccepted)
    (fun _fragments_to_replay replay_to_accept => replay_to_accept)

theorem ay_upfd_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPFDReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_upfd_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPFDReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_upfd_chain_digest
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDDigestChain fragmentDigest digestLinks chainedFragments := by
  intro accepted
  exact ay_upfd_conj_left
    (AyUPFDDigestChain fragmentDigest digestLinks chainedFragments)
    (AyUPFDConj
      (AyUPFDArchiveMembership chainedFragments archiveMember
        archiveAccepted)
      (AyUPFDConj
        (AyUPFDFrameLineage frame frameFresh chainedFragments)
        (AyUPFDConj
          (AyUPFDDependencyCoverage chainedFragments dependencyCoverage
            emptyClause)
          (AyUPFDConj
            (AyUPFDCheckerReplay chainedFragments checkerReplay
              replayAccepted)
            (AyUPFDReconstruction emptyClause visibleUnsat
              originalUnsat)))))
    accepted

theorem ay_upfd_chain_archive
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDArchiveMembership chainedFragments archiveMember
      archiveAccepted := by
  intro accepted
  exact accepted
    (AyUPFDArchiveMembership chainedFragments archiveMember archiveAccepted)
    (fun _digest tail =>
      tail (AyUPFDArchiveMembership chainedFragments archiveMember
        archiveAccepted)
        (fun archive _rest => archive))

theorem ay_upfd_chain_frame
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDFrameLineage frame frameFresh chainedFragments := by
  intro accepted
  exact accepted (AyUPFDFrameLineage frame frameFresh chainedFragments)
    (fun _digest tail =>
      tail (AyUPFDFrameLineage frame frameFresh chainedFragments)
        (fun _archive rest =>
          rest (AyUPFDFrameLineage frame frameFresh chainedFragments)
            (fun lineage _tail => lineage)))

theorem ay_upfd_chain_coverage
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDDependencyCoverage chainedFragments dependencyCoverage
      emptyClause := by
  intro accepted
  exact accepted
    (AyUPFDDependencyCoverage chainedFragments dependencyCoverage
      emptyClause)
    (fun _digest tail =>
      tail
        (AyUPFDDependencyCoverage chainedFragments dependencyCoverage
          emptyClause)
        (fun _archive rest =>
          rest
            (AyUPFDDependencyCoverage chainedFragments dependencyCoverage
              emptyClause)
            (fun _lineage tail2 =>
              tail2
                (AyUPFDDependencyCoverage chainedFragments
                  dependencyCoverage emptyClause)
                (fun coverage _tail => coverage))))

theorem ay_upfd_chain_replay
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDCheckerReplay chainedFragments checkerReplay replayAccepted := by
  intro accepted
  exact accepted
    (AyUPFDCheckerReplay chainedFragments checkerReplay replayAccepted)
    (fun _digest tail =>
      tail (AyUPFDCheckerReplay chainedFragments checkerReplay replayAccepted)
        (fun _archive rest =>
          rest (AyUPFDCheckerReplay chainedFragments checkerReplay
            replayAccepted)
            (fun _lineage tail2 =>
              tail2
                (AyUPFDCheckerReplay chainedFragments checkerReplay
                  replayAccepted)
                (fun _coverage tail3 =>
                  tail3
                    (AyUPFDCheckerReplay chainedFragments checkerReplay
                      replayAccepted)
                    (fun replay _reconstruction => replay)))))

theorem ay_upfd_chain_reconstruction
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDReconstruction emptyClause visibleUnsat originalUnsat := by
  intro accepted
  exact accepted (AyUPFDReconstruction emptyClause visibleUnsat
    originalUnsat)
    (fun _digest tail =>
      tail (AyUPFDReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _archive rest =>
          rest (AyUPFDReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _lineage tail2 =>
              tail2
                (AyUPFDReconstruction emptyClause visibleUnsat
                  originalUnsat)
                (fun _coverage tail3 =>
                  tail3
                    (AyUPFDReconstruction emptyClause visibleUnsat
                      originalUnsat)
                    (fun _replay reconstruction => reconstruction)))))

theorem ay_upfd_chain_fragments
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    chainedFragments := by
  intro accepted
  have chain :
      AyUPFDDigestChain fragmentDigest digestLinks chainedFragments :=
    ay_upfd_chain_digest fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  exact ay_upfd_chained_fragments_from_digest fragmentDigest digestLinks
    chainedFragments chain

theorem ay_upfd_chain_archive_accepted
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    archiveAccepted := by
  intro accepted
  have fragments : chainedFragments :=
    ay_upfd_chain_fragments fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have archive :
      AyUPFDArchiveMembership chainedFragments archiveMember
        archiveAccepted :=
    ay_upfd_chain_archive fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have member : archiveMember :=
    ay_upfd_archive_member chainedFragments archiveMember archiveAccepted
      archive fragments
  exact ay_upfd_archive_accepted chainedFragments archiveMember
    archiveAccepted archive member

theorem ay_upfd_chain_empty_clause
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    emptyClause := by
  intro accepted
  have fragments : chainedFragments :=
    ay_upfd_chain_fragments fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have coverage :
      AyUPFDDependencyCoverage chainedFragments dependencyCoverage
        emptyClause :=
    ay_upfd_chain_coverage fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have covered : dependencyCoverage :=
    ay_upfd_dependency_coverage chainedFragments dependencyCoverage
      emptyClause coverage fragments
  exact ay_upfd_empty_clause chainedFragments dependencyCoverage emptyClause
    coverage covered

theorem ay_upfd_chain_replay_accepted
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    replayAccepted := by
  intro accepted
  have fragments : chainedFragments :=
    ay_upfd_chain_fragments fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have replay :
      AyUPFDCheckerReplay chainedFragments checkerReplay replayAccepted :=
    ay_upfd_chain_replay fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have transcript : checkerReplay :=
    ay_upfd_replay_transcript chainedFragments checkerReplay replayAccepted
      replay fragments
  exact ay_upfd_replay_accepted chainedFragments checkerReplay
    replayAccepted replay transcript

theorem ay_upfd_accepted_chain_original_unsat
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  have empty : emptyClause :=
    ay_upfd_chain_empty_clause fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have reconstruction :
      AyUPFDReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_upfd_chain_reconstruction fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat
      accepted
  have visible : visibleUnsat :=
    ay_upfd_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_upfd_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_upfd_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPFDPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upfd_disj_right noClaim originalUnsat unsat

theorem ay_upfd_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPFDPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upfd_disj_left noClaim originalUnsat no_claim

theorem ay_upfd_accepted_chain_publish_sound
    (fragmentDigest : Prop) (digestLinks : Prop)
    (chainedFragments : Prop) (archiveMember : Prop)
    (archiveAccepted : Prop) (frame : Prop) (frameFresh : Prop)
    (dependencyCoverage : Prop) (emptyClause : Prop)
    (checkerReplay : Prop) (replayAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPFDAcceptedChain fragmentDigest digestLinks chainedFragments
      archiveMember archiveAccepted frame frameFresh dependencyCoverage
      emptyClause checkerReplay replayAccepted visibleUnsat originalUnsat ->
    AyUPFDPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_upfd_public_unsat_report noClaim originalUnsat
    (ay_upfd_accepted_chain_original_unsat fragmentDigest digestLinks
      chainedFragments archiveMember archiveAccepted frame frameFresh
      dependencyCoverage emptyClause checkerReplay replayAccepted
      visibleUnsat originalUnsat accepted)

theorem ay_upfd_bad_chain_no_claim
    (brokenDigestLink : Prop) (missingFragment : Prop)
    (uncoveredDependency : Prop) (staleFrame : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPFDBadChain brokenDigestLink missingFragment uncoveredDependency
      staleFrame replayRejected noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_upfd_bad_chain_recompute
    (brokenDigestLink : Prop) (missingFragment : Prop)
    (uncoveredDependency : Prop) (staleFrame : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPFDBadChain brokenDigestLink missingFragment uncoveredDependency
      staleFrame replayRejected noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_upfd_bad_chain_public_no_claim
    (brokenDigestLink : Prop) (missingFragment : Prop)
    (uncoveredDependency : Prop) (staleFrame : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPFDBadChain brokenDigestLink missingFragment uncoveredDependency
      staleFrame replayRejected noClaim recompute ->
    AyUPFDPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upfd_public_no_claim_report noClaim originalUnsat
    (ay_upfd_bad_chain_no_claim brokenDigestLink missingFragment
      uncoveredDependency staleFrame replayRejected noClaim recompute bad)

theorem ay_upfd_bad_chain_cannot_publish
    (brokenDigestLink : Prop) (missingFragment : Prop)
    (uncoveredDependency : Prop) (staleFrame : Prop)
    (replayRejected : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPFDBadChain brokenDigestLink missingFragment uncoveredDependency
      staleFrame replayRejected noClaim recompute ->
    AyUPFDConj noClaim recompute := by
  intro bad
  exact bad (AyUPFDConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

