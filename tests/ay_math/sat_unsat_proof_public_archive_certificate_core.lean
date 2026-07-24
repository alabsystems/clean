-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded public UNSAT proof archive-certificate soundness for ay.
-- Propositions stand for archive membership, digest roots, dependency coverage,
-- empty-clause witnesses, original reconstruction, and no-claim/recompute
-- diagnostics for stale or partial archive certificates.

def AyUPACConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPACDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPACMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPACArchiveMembership
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) :=
  AyUPACConj archiveEntry
    (AyUPACConj
      (AyUPACMap archiveEntry membershipProof)
      (AyUPACMap membershipProof archivedProof))

def AyUPACDigestRoot
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :=
  AyUPACConj
    (AyUPACMap archivedProof digestRoot)
    (AyUPACMap digestRoot rootAccepted)

def AyUPACDependencyCoverage
    (archivedProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUPACConj
    (AyUPACMap archivedProof dependencyCoverage)
    (AyUPACMap dependencyCoverage emptyClause)

def AyUPACReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPACConj
    (AyUPACMap emptyClause visibleUnsat)
    (AyUPACMap visibleUnsat originalUnsat)

def AyUPACArchiveCertificate
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPACConj
    (AyUPACArchiveMembership archiveEntry membershipProof archivedProof)
    (AyUPACConj
      (AyUPACDigestRoot archivedProof digestRoot rootAccepted)
      (AyUPACConj
        (AyUPACDependencyCoverage archivedProof dependencyCoverage
          emptyClause)
        (AyUPACReconstruction emptyClause visibleUnsat originalUnsat)))

def AyUPACBadCertificate
    (staleCertificate : Prop) (partialCertificate : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPACConj
    (AyUPACConj noClaim recompute)
    (AyUPACDisj staleCertificate partialCertificate)

def AyUPACPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPACDisj noClaim originalUnsat

theorem ay_upac_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPACConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upac_conj_left
    (p : Prop) (q : Prop) :
    AyUPACConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upac_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPACDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upac_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPACDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upac_archive_entry
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) :
    AyUPACArchiveMembership archiveEntry membershipProof archivedProof ->
    archiveEntry := by
  intro membership
  exact ay_upac_conj_left archiveEntry
    (AyUPACConj
      (AyUPACMap archiveEntry membershipProof)
      (AyUPACMap membershipProof archivedProof))
    membership

theorem ay_upac_membership_proof
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) :
    AyUPACArchiveMembership archiveEntry membershipProof archivedProof ->
    membershipProof := by
  intro membership
  exact membership membershipProof
    (fun entry tail =>
      tail membershipProof
        (fun entry_to_membership _membership_to_archive =>
          entry_to_membership entry))

theorem ay_upac_archived_proof
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) :
    AyUPACArchiveMembership archiveEntry membershipProof archivedProof ->
    archivedProof := by
  intro membership
  exact membership archivedProof
    (fun entry tail =>
      tail archivedProof
        (fun entry_to_membership membership_to_archive =>
          membership_to_archive (entry_to_membership entry)))

theorem ay_upac_digest_root_value
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :
    AyUPACDigestRoot archivedProof digestRoot rootAccepted ->
    archivedProof ->
    digestRoot := by
  intro root
  exact root (archivedProof -> digestRoot)
    (fun proof_to_root _root_to_accept => proof_to_root)

theorem ay_upac_root_accepted
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) :
    AyUPACDigestRoot archivedProof digestRoot rootAccepted ->
    digestRoot ->
    rootAccepted := by
  intro root
  exact root (digestRoot -> rootAccepted)
    (fun _proof_to_root root_to_accept => root_to_accept)

theorem ay_upac_dependency_coverage
    (archivedProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUPACDependencyCoverage archivedProof dependencyCoverage
      emptyClause ->
    archivedProof ->
    dependencyCoverage := by
  intro coverage
  exact coverage (archivedProof -> dependencyCoverage)
    (fun proof_to_coverage _coverage_to_empty => proof_to_coverage)

theorem ay_upac_dependency_empty_clause
    (archivedProof : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUPACDependencyCoverage archivedProof dependencyCoverage
      emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _proof_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_upac_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_upac_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_upac_certificate_membership
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUPACArchiveMembership archiveEntry membershipProof archivedProof := by
  intro certificate
  exact ay_upac_conj_left
    (AyUPACArchiveMembership archiveEntry membershipProof archivedProof)
    (AyUPACConj
      (AyUPACDigestRoot archivedProof digestRoot rootAccepted)
      (AyUPACConj
        (AyUPACDependencyCoverage archivedProof dependencyCoverage
          emptyClause)
        (AyUPACReconstruction emptyClause visibleUnsat originalUnsat)))
    certificate

theorem ay_upac_certificate_digest_root
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUPACDigestRoot archivedProof digestRoot rootAccepted := by
  intro certificate
  exact certificate (AyUPACDigestRoot archivedProof digestRoot rootAccepted)
    (fun _membership tail =>
      tail (AyUPACDigestRoot archivedProof digestRoot rootAccepted)
        (fun root _rest => root))

theorem ay_upac_certificate_coverage
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUPACDependencyCoverage archivedProof dependencyCoverage
      emptyClause := by
  intro certificate
  exact certificate
    (AyUPACDependencyCoverage archivedProof dependencyCoverage emptyClause)
    (fun _membership tail =>
      tail
        (AyUPACDependencyCoverage archivedProof dependencyCoverage
          emptyClause)
        (fun _root rest =>
          rest
            (AyUPACDependencyCoverage archivedProof dependencyCoverage
              emptyClause)
            (fun coverage _reconstruction => coverage)))

theorem ay_upac_certificate_reconstruction
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUPACReconstruction emptyClause visibleUnsat originalUnsat := by
  intro certificate
  exact certificate
    (AyUPACReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _membership tail =>
      tail (AyUPACReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _root rest =>
          rest (AyUPACReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage reconstruction => reconstruction)))

theorem ay_upac_certificate_root_accepted
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    rootAccepted := by
  intro certificate
  have membership :
      AyUPACArchiveMembership archiveEntry membershipProof archivedProof :=
    ay_upac_certificate_membership archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat certificate
  have root :
      AyUPACDigestRoot archivedProof digestRoot rootAccepted :=
    ay_upac_certificate_digest_root archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat certificate
  have archived : archivedProof :=
    ay_upac_archived_proof archiveEntry membershipProof archivedProof
      membership
  have digest : digestRoot :=
    ay_upac_digest_root_value archivedProof digestRoot rootAccepted
      root archived
  exact ay_upac_root_accepted archivedProof digestRoot rootAccepted
    root digest

theorem ay_upac_certificate_empty_clause
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro certificate
  have membership :
      AyUPACArchiveMembership archiveEntry membershipProof archivedProof :=
    ay_upac_certificate_membership archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat certificate
  have coverage :
      AyUPACDependencyCoverage archivedProof dependencyCoverage emptyClause :=
    ay_upac_certificate_coverage archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat certificate
  have archived : archivedProof :=
    ay_upac_archived_proof archiveEntry membershipProof archivedProof
      membership
  have covered : dependencyCoverage :=
    ay_upac_dependency_coverage archivedProof dependencyCoverage
      emptyClause coverage archived
  exact ay_upac_dependency_empty_clause archivedProof dependencyCoverage
    emptyClause coverage covered

theorem ay_upac_archive_certificate_original_unsat
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro certificate
  have empty : emptyClause :=
    ay_upac_certificate_empty_clause archiveEntry membershipProof
      archivedProof digestRoot rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat certificate
  have reconstruction :
      AyUPACReconstruction emptyClause visibleUnsat originalUnsat :=
    ay_upac_certificate_reconstruction archiveEntry membershipProof
      archivedProof digestRoot rootAccepted dependencyCoverage emptyClause
      visibleUnsat originalUnsat certificate
  have visible : visibleUnsat :=
    ay_upac_visible_unsat emptyClause visibleUnsat originalUnsat
      reconstruction empty
  exact ay_upac_original_unsat_from_visible emptyClause visibleUnsat
    originalUnsat reconstruction visible

theorem ay_upac_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPACPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upac_disj_right noClaim originalUnsat unsat

theorem ay_upac_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPACPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upac_disj_left noClaim originalUnsat no_claim

theorem ay_upac_archive_certificate_publish_sound
    (archiveEntry : Prop) (membershipProof : Prop)
    (archivedProof : Prop) (digestRoot : Prop)
    (rootAccepted : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUPACArchiveCertificate archiveEntry membershipProof archivedProof
      digestRoot rootAccepted dependencyCoverage emptyClause visibleUnsat
      originalUnsat ->
    AyUPACPublicReport noClaim originalUnsat := by
  intro certificate
  exact ay_upac_public_unsat_report noClaim originalUnsat
    (ay_upac_archive_certificate_original_unsat archiveEntry
      membershipProof archivedProof digestRoot rootAccepted dependencyCoverage
      emptyClause visibleUnsat originalUnsat certificate)

theorem ay_upac_bad_certificate_no_claim
    (staleCertificate : Prop) (partialCertificate : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPACBadCertificate staleCertificate partialCertificate
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun diagnostics _reason =>
      diagnostics noClaim
        (fun no_claim _recompute => no_claim))

theorem ay_upac_bad_certificate_recompute
    (staleCertificate : Prop) (partialCertificate : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPACBadCertificate staleCertificate partialCertificate
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun diagnostics _reason =>
      diagnostics recompute
        (fun _no_claim recompute_required => recompute_required))

theorem ay_upac_bad_certificate_public_no_claim
    (staleCertificate : Prop) (partialCertificate : Prop)
    (noClaim : Prop) (originalUnsat : Prop) (recompute : Prop) :
    AyUPACBadCertificate staleCertificate partialCertificate
      noClaim recompute ->
    AyUPACPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upac_public_no_claim_report noClaim originalUnsat
    (ay_upac_bad_certificate_no_claim staleCertificate partialCertificate
      noClaim recompute bad)

theorem ay_upac_bad_certificate_cannot_publish_unsat
    (staleCertificate : Prop) (partialCertificate : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPACBadCertificate staleCertificate partialCertificate
      noClaim recompute ->
    AyUPACConj noClaim recompute := by
  intro bad
  exact bad (AyUPACConj noClaim recompute)
    (fun diagnostics _reason => diagnostics)

