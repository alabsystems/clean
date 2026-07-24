-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT core minimization archive soundness for ay. Propositions stand
-- for full proof streams, minimized cores, archive membership, dependency
-- coverage, empty-clause witnesses, original-formula reconstruction, and
-- no-claim/recompute diagnostics for omitted required dependencies.

def AyUCMAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCMADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCMAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCMAProjection
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) :=
  AyUCMAConj fullProof
    (AyUCMAConj projectionWitness
      (AyUCMAMap fullProof minimizedCore))

def AyUCMAArchiveMembership
    (minimizedCore : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) :=
  AyUCMAConj minimizedCore
    (AyUCMAConj archiveEntry
      (AyUCMAMap minimizedCore archivedCore))

def AyUCMADependencyCoverage
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :=
  AyUCMAConj
    (AyUCMAMap archivedCore dependencyCoverage)
    (AyUCMAMap dependencyCoverage emptyClause)

def AyUCMAReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCMAConj
    (AyUCMAMap emptyClause visibleUnsat)
    (AyUCMAMap visibleUnsat originalUnsat)

def AyUCMAMinimizedCoreArchiveProof
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUCMAConj
    (AyUCMAProjection fullProof minimizedCore projectionWitness)
    (AyUCMAConj
      (AyUCMAArchiveMembership minimizedCore archiveEntry archivedCore)
      (AyUCMAConj
        (AyUCMADependencyCoverage
          archivedCore dependencyCoverage emptyClause)
        (AyUCMAReconstruction emptyClause visibleUnsat originalUnsat)))

def AyUCMAOmittedDependency
    (omittedDependency : Prop) (coverageMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUCMAConj
    (AyUCMAConj noClaim recompute)
    (AyUCMADisj omittedDependency coverageMismatch)

def AyUCMAPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCMADisj noClaim originalUnsat

theorem ay_ucma_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCMAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucma_conj_left
    (p : Prop) (q : Prop) :
    AyUCMAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucma_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCMADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucma_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCMADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucma_project_core
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) :
    AyUCMAProjection fullProof minimizedCore projectionWitness ->
    minimizedCore := by
  intro projection
  exact projection minimizedCore
    (fun full tail =>
      tail minimizedCore
        (fun _witness full_to_core => full_to_core full))

theorem ay_ucma_archive_core
    (minimizedCore : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) :
    AyUCMAArchiveMembership minimizedCore archiveEntry archivedCore ->
    archivedCore := by
  intro membership
  exact membership archivedCore
    (fun core tail =>
      tail archivedCore
        (fun _entry core_to_archive => core_to_archive core))

theorem ay_ucma_dependency_coverage
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUCMADependencyCoverage archivedCore dependencyCoverage emptyClause ->
    archivedCore ->
    dependencyCoverage := by
  intro coverage
  exact coverage (archivedCore -> dependencyCoverage)
    (fun core_to_coverage _coverage_to_empty => core_to_coverage)

theorem ay_ucma_covered_empty_clause
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) :
    AyUCMADependencyCoverage archivedCore dependencyCoverage emptyClause ->
    dependencyCoverage ->
    emptyClause := by
  intro coverage
  exact coverage (dependencyCoverage -> emptyClause)
    (fun _core_to_coverage coverage_to_empty => coverage_to_empty)

theorem ay_ucma_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_ucma_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_ucma_proof_projection
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    AyUCMAProjection fullProof minimizedCore projectionWitness := by
  intro proof
  exact ay_ucma_conj_left
    (AyUCMAProjection fullProof minimizedCore projectionWitness)
    (AyUCMAConj
      (AyUCMAArchiveMembership minimizedCore archiveEntry archivedCore)
      (AyUCMAConj
        (AyUCMADependencyCoverage archivedCore dependencyCoverage emptyClause)
        (AyUCMAReconstruction emptyClause visibleUnsat originalUnsat)))
    proof

theorem ay_ucma_proof_archive
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    AyUCMAArchiveMembership minimizedCore archiveEntry archivedCore := by
  intro proof
  exact proof (AyUCMAArchiveMembership minimizedCore archiveEntry archivedCore)
    (fun _projection tail =>
      tail (AyUCMAArchiveMembership minimizedCore archiveEntry archivedCore)
        (fun archive _rest => archive))

theorem ay_ucma_proof_coverage
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    AyUCMADependencyCoverage archivedCore dependencyCoverage emptyClause := by
  intro proof
  exact proof
    (AyUCMADependencyCoverage archivedCore dependencyCoverage emptyClause)
    (fun _projection tail =>
      tail
        (AyUCMADependencyCoverage archivedCore dependencyCoverage emptyClause)
        (fun _archive rest =>
          rest
            (AyUCMADependencyCoverage
              archivedCore dependencyCoverage emptyClause)
            (fun coverage _reconstruction => coverage)))

theorem ay_ucma_proof_reconstruction
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    AyUCMAReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUCMAReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _projection tail =>
      tail (AyUCMAReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _archive rest =>
          rest (AyUCMAReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _coverage reconstruction => reconstruction)))

theorem ay_ucma_proof_empty_clause
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    emptyClause := by
  intro proof
  exact ay_ucma_covered_empty_clause archivedCore dependencyCoverage emptyClause
    (ay_ucma_proof_coverage fullProof minimizedCore projectionWitness
      archiveEntry archivedCore dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof)
    (ay_ucma_dependency_coverage archivedCore dependencyCoverage emptyClause
      (ay_ucma_proof_coverage fullProof minimizedCore projectionWitness
        archiveEntry archivedCore dependencyCoverage emptyClause visibleUnsat
        originalUnsat proof)
      (ay_ucma_archive_core minimizedCore archiveEntry archivedCore
        (ay_ucma_proof_archive fullProof minimizedCore projectionWitness
          archiveEntry archivedCore dependencyCoverage emptyClause
          visibleUnsat originalUnsat proof)))

theorem ay_ucma_archive_original_unsat
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  exact ay_ucma_original_unsat_from_visible emptyClause visibleUnsat originalUnsat
    (ay_ucma_proof_reconstruction fullProof minimizedCore projectionWitness
      archiveEntry archivedCore dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof)
    (ay_ucma_visible_unsat emptyClause visibleUnsat originalUnsat
      (ay_ucma_proof_reconstruction fullProof minimizedCore projectionWitness
        archiveEntry archivedCore dependencyCoverage emptyClause visibleUnsat
        originalUnsat proof)
      (ay_ucma_proof_empty_clause fullProof minimizedCore projectionWitness
        archiveEntry archivedCore dependencyCoverage emptyClause visibleUnsat
        originalUnsat proof))

theorem ay_ucma_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUCMAPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucma_disj_right noClaim originalUnsat unsat

theorem ay_ucma_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUCMAPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucma_disj_left noClaim originalUnsat no_claim

theorem ay_ucma_minimized_core_archive_publish_sound
    (fullProof : Prop) (minimizedCore : Prop)
    (projectionWitness : Prop) (archiveEntry : Prop)
    (archivedCore : Prop) (dependencyCoverage : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUCMAMinimizedCoreArchiveProof fullProof minimizedCore
      projectionWitness archiveEntry archivedCore dependencyCoverage
      emptyClause visibleUnsat originalUnsat ->
    AyUCMAPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_ucma_public_unsat_report noClaim originalUnsat
    (ay_ucma_archive_original_unsat fullProof minimizedCore projectionWitness
      archiveEntry archivedCore dependencyCoverage emptyClause visibleUnsat
      originalUnsat proof)

theorem ay_ucma_omitted_dependency_no_claim
    (omittedDependency : Prop) (coverageMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCMAOmittedDependency
      omittedDependency coverageMismatch noClaim recompute ->
    noClaim := by
  intro omitted
  exact omitted noClaim
    (fun both _reason =>
      ay_ucma_conj_left noClaim recompute both)

theorem ay_ucma_omitted_dependency_recompute
    (omittedDependency : Prop) (coverageMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUCMAOmittedDependency
      omittedDependency coverageMismatch noClaim recompute ->
    recompute := by
  intro omitted
  exact omitted recompute
    (fun both _reason =>
      both recompute (fun _no_claim hrecompute => hrecompute))

theorem ay_ucma_omitted_dependency_public_no_claim
    (omittedDependency : Prop) (coverageMismatch : Prop)
    (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCMAOmittedDependency
      omittedDependency coverageMismatch noClaim recompute ->
    AyUCMAPublicReport noClaim originalUnsat := by
  intro omitted
  exact ay_ucma_public_no_claim_report noClaim originalUnsat
    (ay_ucma_omitted_dependency_no_claim
      omittedDependency coverageMismatch noClaim recompute omitted)

theorem ay_ucma_omitted_dependency_cannot_publish_unsat
    (omittedDependency : Prop) (coverageMismatch : Prop)
    (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCMAOmittedDependency
      omittedDependency coverageMismatch noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro omitted
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ucma_omitted_dependency_no_claim
      omittedDependency coverageMismatch noClaim recompute omitted)
    unsat
