-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded dependency-digest DAG replay soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for dependency digest vertices
-- and edges, parent coverage, root empty clause, checker transcripts, formula
-- fingerprints, reconstruction evidence, and fail-closed no-claim/recompute
-- diagnostics.

def AyUPDDConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPDDDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPDDMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPDDDigestDag
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) :=
  AyUPDDConj digestVertices
    (AyUPDDConj
      (AyUPDDMap digestVertices digestEdges)
      (AyUPDDMap digestEdges dagReplay))

def AyUPDDParentCoverage
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :=
  AyUPDDConj
    (AyUPDDMap dagReplay parentCoverage)
    (AyUPDDMap parentCoverage rootEmptyClause)

def AyUPDDCheckerTranscript
    (dagReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :=
  AyUPDDConj
    (AyUPDDMap dagReplay checkerTranscript)
    (AyUPDDMap checkerTranscript checkerAccepted)

def AyUPDDFormulaFingerprint
    (dagReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUPDDConj
    (AyUPDDMap dagReplay formulaFingerprint)
    (AyUPDDMap formulaFingerprint fingerprintAccepted)

def AyUPDDReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPDDConj reconstructionEvidence
    (AyUPDDConj
      (AyUPDDMap rootEmptyClause visibleUnsat)
      (AyUPDDMap visibleUnsat originalUnsat))

def AyUPDDAcceptedEvidence
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPDDConj
    (AyUPDDDigestDag digestVertices digestEdges dagReplay)
    (AyUPDDConj
      (AyUPDDParentCoverage dagReplay parentCoverage rootEmptyClause)
      (AyUPDDConj
        (AyUPDDCheckerTranscript dagReplay checkerTranscript checkerAccepted)
        (AyUPDDConj
          (AyUPDDFormulaFingerprint dagReplay formulaFingerprint
            fingerprintAccepted)
          (AyUPDDReconstruction rootEmptyClause reconstructionEvidence
            visibleUnsat originalUnsat))))

def AyUPDDAcceptedDag
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPDDConj
    (AyUPDDAcceptedEvidence digestVertices digestEdges dagReplay
      parentCoverage rootEmptyClause checkerTranscript checkerAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyUPDDBadDag
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUPDDConj
    (AyUPDDConj noClaim recompute)
    (AyUPDDDisj malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))))

def AyUPDDPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPDDDisj noClaim originalUnsat

theorem ay_updd_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPDDConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_updd_conj_left
    (p : Prop) (q : Prop) :
    AyUPDDConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_updd_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPDDDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_updd_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPDDDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_updd_digest_vertices
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) :
    AyUPDDDigestDag digestVertices digestEdges dagReplay ->
    digestVertices := by
  intro dag
  exact dag digestVertices
    (fun vertices _tail => vertices)

theorem ay_updd_digest_edges
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) :
    AyUPDDDigestDag digestVertices digestEdges dagReplay ->
    digestEdges := by
  intro dag
  exact dag digestEdges
    (fun (vertices : digestVertices) tail =>
      tail digestEdges
        (fun vertices_to_edges _edges_to_replay =>
          vertices_to_edges vertices))

theorem ay_updd_dag_replay
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) :
    AyUPDDDigestDag digestVertices digestEdges dagReplay ->
    dagReplay := by
  intro dag
  exact dag dagReplay
    (fun (vertices : digestVertices) tail =>
      tail dagReplay
        (fun vertices_to_edges edges_to_replay =>
          edges_to_replay (vertices_to_edges vertices)))

theorem ay_updd_parent_coverage
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUPDDParentCoverage dagReplay parentCoverage rootEmptyClause ->
    dagReplay ->
    parentCoverage := by
  intro parents
  exact parents (dagReplay -> parentCoverage)
    (fun replay_to_parents _parents_to_empty => replay_to_parents)

theorem ay_updd_root_empty_clause
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUPDDParentCoverage dagReplay parentCoverage rootEmptyClause ->
    parentCoverage ->
    rootEmptyClause := by
  intro parents
  exact parents (parentCoverage -> rootEmptyClause)
    (fun _replay_to_parents parents_to_empty => parents_to_empty)

theorem ay_updd_checker_transcript
    (dagReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPDDCheckerTranscript dagReplay checkerTranscript checkerAccepted ->
    dagReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (dagReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_updd_checker_accepted
    (dagReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) :
    AyUPDDCheckerTranscript dagReplay checkerTranscript checkerAccepted ->
    checkerTranscript ->
    checkerAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> checkerAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_updd_formula_fingerprint
    (dagReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPDDFormulaFingerprint dagReplay formulaFingerprint
      fingerprintAccepted ->
    dagReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (dagReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_updd_fingerprint_accepted
    (dagReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPDDFormulaFingerprint dagReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_updd_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDDReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_updd_conj_left reconstructionEvidence
    (AyUPDDConj
      (AyUPDDMap rootEmptyClause visibleUnsat)
      (AyUPDDMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_updd_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDDReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_updd_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDDReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_updd_accepted_evidence
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDDAcceptedDag digestVertices digestEdges dagReplay parentCoverage
      rootEmptyClause checkerTranscript checkerAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUPDDAcceptedEvidence digestVertices digestEdges dagReplay
      parentCoverage rootEmptyClause checkerTranscript checkerAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact ay_updd_conj_left
    (AyUPDDAcceptedEvidence digestVertices digestEdges dagReplay
      parentCoverage rootEmptyClause checkerTranscript checkerAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_updd_accepted_original_unsat
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPDDAcceptedDag digestVertices digestEdges dagReplay parentCoverage
      rootEmptyClause checkerTranscript checkerAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_updd_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPDDPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_updd_disj_right noClaim originalUnsat unsat

theorem ay_updd_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPDDPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_updd_disj_left noClaim originalUnsat no_claim

theorem ay_updd_accepted_dag_publish_sound
    (digestVertices : Prop) (digestEdges : Prop)
    (dagReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPDDAcceptedDag digestVertices digestEdges dagReplay parentCoverage
      rootEmptyClause checkerTranscript checkerAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUPDDPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_updd_public_unsat_report noClaim originalUnsat
    (ay_updd_accepted_original_unsat digestVertices digestEdges dagReplay
      parentCoverage rootEmptyClause checkerTranscript checkerAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat accepted)

theorem ay_updd_bad_dag_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_updd_conj_left noClaim recompute fail_closed)

theorem ay_updd_bad_dag_recompute
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_updd_bad_dag_public_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    AyUPDDPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_updd_public_no_claim_report noClaim originalUnsat
    (ay_updd_bad_dag_no_claim malformedDag missingParent digestMismatch
      staleFingerprint uncheckedTranscript noClaim recompute bad)

theorem ay_updd_bad_dag_cannot_publish
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_updd_bad_dag_no_claim malformedDag missingParent digestMismatch
      staleFingerprint uncheckedTranscript noClaim recompute bad)
    unsat

theorem ay_updd_malformed_dag_forces_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    malformedDag ->
    AyUPDDConj noClaim recompute ->
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro malformed
  intro fail_closed
  exact ay_updd_conj_intro
    (AyUPDDConj noClaim recompute)
    (AyUPDDDisj malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_updd_disj_left malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)))
      malformed)

theorem ay_updd_missing_parent_forces_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingParent ->
    AyUPDDConj noClaim recompute ->
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_updd_conj_intro
    (AyUPDDConj noClaim recompute)
    (AyUPDDDisj malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_updd_disj_right malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)))
      (ay_updd_disj_left missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))
        missing))

theorem ay_updd_digest_mismatch_forces_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    digestMismatch ->
    AyUPDDConj noClaim recompute ->
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_updd_conj_intro
    (AyUPDDConj noClaim recompute)
    (AyUPDDDisj malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_updd_disj_right malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)))
      (ay_updd_disj_right missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))
        (ay_updd_disj_left digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)
          mismatch)))

theorem ay_updd_stale_fingerprint_forces_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    AyUPDDConj noClaim recompute ->
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_updd_conj_intro
    (AyUPDDConj noClaim recompute)
    (AyUPDDDisj malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_updd_disj_right malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)))
      (ay_updd_disj_right missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))
        (ay_updd_disj_right digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)
          (ay_updd_disj_left staleFingerprint uncheckedTranscript stale))))

theorem ay_updd_unchecked_transcript_forces_no_claim
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUPDDConj noClaim recompute ->
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_updd_conj_intro
    (AyUPDDConj noClaim recompute)
    (AyUPDDDisj malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_updd_disj_right malformedDag
      (AyUPDDDisj missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)))
      (ay_updd_disj_right missingParent
        (AyUPDDDisj digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript))
        (ay_updd_disj_right digestMismatch
          (AyUPDDDisj staleFingerprint uncheckedTranscript)
          (ay_updd_disj_right staleFingerprint uncheckedTranscript
            unchecked))))

theorem ay_updd_unchecked_transcript_cannot_publish
    (malformedDag : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPDDBadDag malformedDag missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_updd_bad_dag_cannot_publish malformedDag missingParent
    digestMismatch staleFingerprint uncheckedTranscript noClaim recompute
    originalUnsat bad
