-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT core digest publication soundness for ay. Propositions stand
-- for core proofs, dependency coverage, digest rollups, empty-clause witnesses,
-- original reconstruction, and no-claim/recompute diagnostics for stale or
-- partial core digests.

def AyUCDPConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCDPDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCDPMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCDPCoreCoverage
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUCDPConj coreProof
    (AyUCDPConj
      (AyUCDPMap coreProof dependencyCoverage)
      (AyUCDPMap dependencyCoverage emptyClause))

def AyUCDPDigestRollup
    (coreProof : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop) :=
  AyUCDPConj
    (AyUCDPMap coreProof coreDigest)
    (AyUCDPConj
      (AyUCDPMap coreDigest publishedDigest)
      (AyUCDPMap publishedDigest digestAccepted))

def AyUCDPReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCDPConj
    (AyUCDPMap emptyClause visibleUnsat)
    (AyUCDPMap visibleUnsat originalUnsat)

def AyUCDPPublicationProof
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCDPConj
    (AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause)
    (AyUCDPConj
      (AyUCDPDigestRollup coreProof coreDigest publishedDigest
        digestAccepted)
      (AyUCDPReconstruction emptyClause visibleUnsat originalUnsat))

def AyUCDPBadCoreDigest
    (staleCoreDigest : Prop) (partialCoreDigest : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCDPConj
    (AyUCDPConj noClaim recompute)
    (AyUCDPDisj staleCoreDigest partialCoreDigest)

def AyUCDPPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCDPDisj noClaim originalUnsat

theorem ay_ucdp_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCDPConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucdp_conj_left
    (p : Prop) (q : Prop) :
    AyUCDPConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucdp_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCDPDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucdp_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCDPDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucdp_core_proof
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause ->
    coreProof := by
  intro coverage
  exact ay_ucdp_conj_left coreProof
    (AyUCDPConj
      (AyUCDPMap coreProof dependencyCoverage)
      (AyUCDPMap dependencyCoverage emptyClause))
    coverage

theorem ay_ucdp_dependency_coverage
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause ->
    dependencyCoverage := by
  intro coverage
  exact coverage dependencyCoverage
    (fun core tail =>
      tail dependencyCoverage
        (fun core_to_coverage _coverage_to_empty =>
          core_to_coverage core))

theorem ay_ucdp_empty_clause
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause ->
    emptyClause := by
  intro coverage
  exact coverage emptyClause
    (fun core tail =>
      tail emptyClause
        (fun core_to_coverage coverage_to_empty =>
          coverage_to_empty (core_to_coverage core)))

theorem ay_ucdp_core_digest_value
    (coreProof : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop) :
    AyUCDPDigestRollup coreProof coreDigest publishedDigest
      digestAccepted ->
    coreProof ->
    coreDigest := by
  intro rollup
  exact rollup (coreProof -> coreDigest)
    (fun core_to_digest _tail => core_to_digest)

theorem ay_ucdp_published_digest_value
    (coreProof : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop) :
    AyUCDPDigestRollup coreProof coreDigest publishedDigest
      digestAccepted ->
    coreDigest ->
    publishedDigest := by
  intro rollup
  exact rollup (coreDigest -> publishedDigest)
    (fun _core_to_digest tail =>
      tail (coreDigest -> publishedDigest)
        (fun digest_to_published _published_to_accept =>
          digest_to_published))

theorem ay_ucdp_digest_accepted
    (coreProof : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop) :
    AyUCDPDigestRollup coreProof coreDigest publishedDigest
      digestAccepted ->
    publishedDigest ->
    digestAccepted := by
  intro rollup
  exact rollup (publishedDigest -> digestAccepted)
    (fun _core_to_digest tail =>
      tail (publishedDigest -> digestAccepted)
        (fun _digest_to_published published_to_accept =>
          published_to_accept))

theorem ay_ucdp_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDPReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucdp_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCDPReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucdp_proof_core_coverage
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDPPublicationProof coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause := by
  intro proof
  exact ay_ucdp_conj_left
    (AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause)
    (AyUCDPConj
      (AyUCDPDigestRollup coreProof coreDigest publishedDigest
        digestAccepted)
      (AyUCDPReconstruction emptyClause visibleUnsat originalUnsat))
    proof

theorem ay_ucdp_proof_digest_rollup
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDPPublicationProof coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUCDPDigestRollup coreProof coreDigest publishedDigest
      digestAccepted := by
  intro proof
  exact proof
    (AyUCDPDigestRollup coreProof coreDigest publishedDigest
      digestAccepted)
    (fun _coverage tail =>
      tail
        (AyUCDPDigestRollup coreProof coreDigest publishedDigest
          digestAccepted)
        (fun rollup _reconstruction => rollup))

theorem ay_ucdp_proof_reconstruction
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDPPublicationProof coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUCDPReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUCDPReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _coverage tail =>
      tail (AyUCDPReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _rollup reconstruction => reconstruction))

theorem ay_ucdp_proof_digest_accepted
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDPPublicationProof coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat ->
    digestAccepted := by
  intro proof
  have coverage :
      AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause :=
    ay_ucdp_proof_core_coverage coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat originalUnsat
      proof
  have rollup :
      AyUCDPDigestRollup coreProof coreDigest publishedDigest
        digestAccepted :=
    ay_ucdp_proof_digest_rollup coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat originalUnsat
      proof
  have core : coreProof :=
    ay_ucdp_core_proof coreProof dependencyCoverage emptyClause coverage
  have digest : coreDigest :=
    ay_ucdp_core_digest_value coreProof coreDigest publishedDigest
      digestAccepted rollup core
  have published : publishedDigest :=
    ay_ucdp_published_digest_value coreProof coreDigest publishedDigest
      digestAccepted rollup digest
  exact ay_ucdp_digest_accepted coreProof coreDigest publishedDigest
    digestAccepted rollup published

theorem ay_ucdp_publication_original_unsat
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCDPPublicationProof coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro proof
  have coverage :
      AyUCDPCoreCoverage coreProof dependencyCoverage emptyClause :=
    ay_ucdp_proof_core_coverage coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat originalUnsat
      proof
  have empty : emptyClause :=
    ay_ucdp_empty_clause coreProof dependencyCoverage emptyClause coverage
  have reconstruction :
      AyUCDPReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_ucdp_proof_reconstruction coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat originalUnsat
      proof
  have visible : visibleUnsat :=
    ay_ucdp_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_ucdp_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_ucdp_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCDPPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucdp_disj_right noClaim originalUnsat unsat

theorem ay_ucdp_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCDPPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucdp_disj_left noClaim originalUnsat no_claim

theorem ay_ucdp_digest_publication_sound
    (coreProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (coreDigest : Prop)
    (publishedDigest : Prop) (digestAccepted : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (noClaim : Prop) :
    AyUCDPPublicationProof coreProof dependencyCoverage emptyClause
      coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUCDPPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_ucdp_public_unsat_report noClaim originalUnsat
    (ay_ucdp_publication_original_unsat coreProof dependencyCoverage
      emptyClause coreDigest publishedDigest digestAccepted visibleUnsat
      originalUnsat proof)

theorem ay_ucdp_bad_digest_no_claim
    (staleCoreDigest : Prop) (partialCoreDigest : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDPBadCoreDigest staleCoreDigest partialCoreDigest
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_ucdp_bad_digest_recompute
    (staleCoreDigest : Prop) (partialCoreDigest : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDPBadCoreDigest staleCoreDigest partialCoreDigest
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_ucdp_bad_digest_public_no_claim
    (staleCoreDigest : Prop) (partialCoreDigest : Prop)
    (noClaim : Prop) (originalUnsat : Prop) (recompute : Prop) :
    AyUCDPBadCoreDigest staleCoreDigest partialCoreDigest
      noClaim recompute ->
    AyUCDPPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucdp_public_no_claim_report noClaim originalUnsat
    (ay_ucdp_bad_digest_no_claim staleCoreDigest partialCoreDigest
      noClaim recompute bad)

theorem ay_ucdp_bad_digest_cannot_publish_unsat
    (staleCoreDigest : Prop) (partialCoreDigest : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCDPBadCoreDigest staleCoreDigest partialCoreDigest
      noClaim recompute ->
    AyUCDPConj noClaim recompute := by
  intro bad
  exact bad (AyUCDPConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

