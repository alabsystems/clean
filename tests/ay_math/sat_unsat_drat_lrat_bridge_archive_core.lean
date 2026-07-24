-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded DRAT/LRAT bridge archive soundness contract for ay. Propositions
-- stand for compact DRAT streams, archive membership, deletion hints, bridge
-- witnesses, LRAT clause dependencies, empty-clause witnesses, original-formula
-- reconstruction, and no-claim/recompute diagnostics for bridge mismatches.

def AyUDLBConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUDLBDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUDLBMap (source : Prop) (target : Prop) :=
  source -> target

def AyUDLBArchiveMembership
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) :=
  AyUDLBConj dratStream
    (AyUDLBConj archiveEntry
      (AyUDLBMap dratStream archivedStream))

def AyUDLBDeletionHints
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) :=
  AyUDLBConj
    (AyUDLBMap archivedStream deletionHints)
    (AyUDLBMap deletionHints hintCheckedStream)

def AyUDLBBridgeWitness
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) :=
  AyUDLBConj
    (AyUDLBMap hintCheckedStream bridgeWitness)
    (AyUDLBMap bridgeWitness lratEvidence)

def AyUDLBClauseDependency
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) :=
  AyUDLBConj
    (AyUDLBMap lratEvidence clauseDependencies)
    (AyUDLBMap clauseDependencies emptyClause)

def AyUDLBReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDLBConj
    (AyUDLBMap emptyClause visibleUnsat)
    (AyUDLBMap visibleUnsat originalUnsat)

def AyUDLBBridgeArchiveProof
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDLBConj
    (AyUDLBArchiveMembership dratStream archiveEntry archivedStream)
    (AyUDLBConj
      (AyUDLBDeletionHints
        archivedStream deletionHints hintCheckedStream)
      (AyUDLBConj
        (AyUDLBBridgeWitness
          hintCheckedStream bridgeWitness lratEvidence)
        (AyUDLBConj
          (AyUDLBClauseDependency
            lratEvidence clauseDependencies emptyClause)
          (AyUDLBReconstruction
            emptyClause visibleUnsat originalUnsat))))

def AyUDLBBridgeMismatch
    (archiveMismatch : Prop) (bridgeMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUDLBConj
    (AyUDLBConj noClaim recompute)
    (AyUDLBDisj archiveMismatch bridgeMismatch)

def AyUDLBPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUDLBDisj noClaim originalUnsat

theorem ay_udlb_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUDLBConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_udlb_conj_left
    (p : Prop) (q : Prop) :
    AyUDLBConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_udlb_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUDLBDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_udlb_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUDLBDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_udlb_archive_stream
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) :
    AyUDLBArchiveMembership dratStream archiveEntry archivedStream ->
    archivedStream := by
  intro membership
  exact membership archivedStream
    (fun stream tail =>
      tail archivedStream
        (fun _entry stream_to_archive => stream_to_archive stream))

theorem ay_udlb_deletion_hints
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) :
    AyUDLBDeletionHints archivedStream deletionHints hintCheckedStream ->
    archivedStream ->
    deletionHints := by
  intro hints
  exact hints (archivedStream -> deletionHints)
    (fun archive_to_hints _hints_to_checked => archive_to_hints)

theorem ay_udlb_hint_checked_stream
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) :
    AyUDLBDeletionHints archivedStream deletionHints hintCheckedStream ->
    deletionHints ->
    hintCheckedStream := by
  intro hints
  exact hints (deletionHints -> hintCheckedStream)
    (fun _archive_to_hints hints_to_checked => hints_to_checked)

theorem ay_udlb_bridge_witness
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) :
    AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence ->
    hintCheckedStream ->
    bridgeWitness := by
  intro bridge
  exact bridge (hintCheckedStream -> bridgeWitness)
    (fun checked_to_bridge _bridge_to_lrat => checked_to_bridge)

theorem ay_udlb_lrat_evidence
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) :
    AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence ->
    bridgeWitness ->
    lratEvidence := by
  intro bridge
  exact bridge (bridgeWitness -> lratEvidence)
    (fun _checked_to_bridge bridge_to_lrat => bridge_to_lrat)

theorem ay_udlb_clause_dependencies
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) :
    AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause ->
    lratEvidence ->
    clauseDependencies := by
  intro dependency
  exact dependency (lratEvidence -> clauseDependencies)
    (fun lrat_to_dependencies _dependencies_to_empty =>
      lrat_to_dependencies)

theorem ay_udlb_empty_clause
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) :
    AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause ->
    clauseDependencies ->
    emptyClause := by
  intro dependency
  exact dependency (clauseDependencies -> emptyClause)
    (fun _lrat_to_dependencies dependencies_to_empty =>
      dependencies_to_empty)

theorem ay_udlb_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_udlb_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_udlb_proof_archive
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    AyUDLBArchiveMembership dratStream archiveEntry archivedStream := by
  intro proof
  exact ay_udlb_conj_left
    (AyUDLBArchiveMembership dratStream archiveEntry archivedStream)
    (AyUDLBConj
      (AyUDLBDeletionHints archivedStream deletionHints hintCheckedStream)
      (AyUDLBConj
        (AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence)
        (AyUDLBConj
          (AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause)
          (AyUDLBReconstruction emptyClause visibleUnsat originalUnsat))))
    proof

theorem ay_udlb_proof_deletions
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    AyUDLBDeletionHints archivedStream deletionHints hintCheckedStream := by
  intro proof
  exact proof
    (AyUDLBDeletionHints archivedStream deletionHints hintCheckedStream)
    (fun _archive tail =>
      tail
        (AyUDLBDeletionHints archivedStream deletionHints hintCheckedStream)
        (fun deletions _rest => deletions))

theorem ay_udlb_proof_bridge
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence := by
  intro proof
  exact proof (AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence)
    (fun _archive tail =>
      tail (AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence)
        (fun _deletions rest =>
          rest (AyUDLBBridgeWitness hintCheckedStream bridgeWitness lratEvidence)
            (fun bridge _tail => bridge)))

theorem ay_udlb_proof_dependencies
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause := by
  intro proof
  exact proof
    (AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause)
    (fun _archive tail =>
      tail (AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause)
        (fun _deletions rest =>
          rest
            (AyUDLBClauseDependency lratEvidence clauseDependencies emptyClause)
            (fun _bridge tail2 =>
              tail2
                (AyUDLBClauseDependency
                  lratEvidence clauseDependencies emptyClause)
                (fun dependency _reconstruction => dependency))))

theorem ay_udlb_proof_reconstruction
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    AyUDLBReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUDLBReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _archive tail =>
      tail (AyUDLBReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _deletions rest =>
          rest (AyUDLBReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _bridge tail2 =>
              tail2 (AyUDLBReconstruction emptyClause visibleUnsat originalUnsat)
                (fun _dependency reconstruction => reconstruction))))

theorem ay_udlb_bridge_archive_empty_clause
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    emptyClause := by
  intro proof
  exact ay_udlb_empty_clause lratEvidence clauseDependencies emptyClause
    (ay_udlb_proof_dependencies dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat proof)
    (ay_udlb_clause_dependencies lratEvidence clauseDependencies emptyClause
      (ay_udlb_proof_dependencies dratStream archiveEntry archivedStream
        deletionHints hintCheckedStream bridgeWitness lratEvidence
        clauseDependencies emptyClause visibleUnsat originalUnsat proof)
      (ay_udlb_lrat_evidence hintCheckedStream bridgeWitness lratEvidence
        (ay_udlb_proof_bridge dratStream archiveEntry archivedStream
          deletionHints hintCheckedStream bridgeWitness lratEvidence
          clauseDependencies emptyClause visibleUnsat originalUnsat proof)
        (ay_udlb_bridge_witness hintCheckedStream bridgeWitness lratEvidence
          (ay_udlb_proof_bridge dratStream archiveEntry archivedStream
            deletionHints hintCheckedStream bridgeWitness lratEvidence
            clauseDependencies emptyClause visibleUnsat originalUnsat proof)
          (ay_udlb_hint_checked_stream archivedStream deletionHints
            hintCheckedStream
            (ay_udlb_proof_deletions dratStream archiveEntry archivedStream
              deletionHints hintCheckedStream bridgeWitness lratEvidence
              clauseDependencies emptyClause visibleUnsat originalUnsat proof)
            (ay_udlb_deletion_hints archivedStream deletionHints
              hintCheckedStream
              (ay_udlb_proof_deletions dratStream archiveEntry archivedStream
                deletionHints hintCheckedStream bridgeWitness lratEvidence
                clauseDependencies emptyClause visibleUnsat originalUnsat proof)
              (ay_udlb_archive_stream dratStream archiveEntry archivedStream
                (ay_udlb_proof_archive dratStream archiveEntry archivedStream
                  deletionHints hintCheckedStream bridgeWitness lratEvidence
                  clauseDependencies emptyClause visibleUnsat originalUnsat
                  proof)))))))

theorem ay_udlb_bridge_archive_original_unsat
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  exact ay_udlb_original_unsat_from_visible emptyClause visibleUnsat originalUnsat
    (ay_udlb_proof_reconstruction dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat proof)
    (ay_udlb_visible_unsat emptyClause visibleUnsat originalUnsat
      (ay_udlb_proof_reconstruction dratStream archiveEntry archivedStream
        deletionHints hintCheckedStream bridgeWitness lratEvidence
        clauseDependencies emptyClause visibleUnsat originalUnsat proof)
      (ay_udlb_bridge_archive_empty_clause dratStream archiveEntry
        archivedStream deletionHints hintCheckedStream bridgeWitness
        lratEvidence clauseDependencies emptyClause visibleUnsat
        originalUnsat proof))

theorem ay_udlb_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUDLBPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_udlb_disj_right noClaim originalUnsat unsat

theorem ay_udlb_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUDLBPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_udlb_disj_left noClaim originalUnsat no_claim

theorem ay_udlb_bridge_archive_publish_sound
    (dratStream : Prop) (archiveEntry : Prop)
    (archivedStream : Prop) (deletionHints : Prop)
    (hintCheckedStream : Prop) (bridgeWitness : Prop)
    (lratEvidence : Prop) (clauseDependencies : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUDLBBridgeArchiveProof dratStream archiveEntry archivedStream
      deletionHints hintCheckedStream bridgeWitness lratEvidence
      clauseDependencies emptyClause visibleUnsat originalUnsat ->
    AyUDLBPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_udlb_public_unsat_report noClaim originalUnsat
    (ay_udlb_bridge_archive_original_unsat dratStream archiveEntry
      archivedStream deletionHints hintCheckedStream bridgeWitness
      lratEvidence clauseDependencies emptyClause visibleUnsat originalUnsat
      proof)

theorem ay_udlb_mismatch_no_claim
    (archiveMismatch : Prop) (bridgeMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDLBBridgeMismatch archiveMismatch bridgeMismatch noClaim recompute ->
    noClaim := by
  intro mismatch
  exact mismatch noClaim
    (fun both _mismatch =>
      ay_udlb_conj_left noClaim recompute both)

theorem ay_udlb_mismatch_recompute
    (archiveMismatch : Prop) (bridgeMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUDLBBridgeMismatch archiveMismatch bridgeMismatch noClaim recompute ->
    recompute := by
  intro mismatch
  exact mismatch recompute
    (fun both _mismatch =>
      both recompute (fun _no_claim hrecompute => hrecompute))

theorem ay_udlb_mismatch_public_no_claim
    (archiveMismatch : Prop) (bridgeMismatch : Prop)
    (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeMismatch archiveMismatch bridgeMismatch noClaim recompute ->
    AyUDLBPublicReport noClaim originalUnsat := by
  intro mismatch
  exact ay_udlb_public_no_claim_report noClaim originalUnsat
    (ay_udlb_mismatch_no_claim
      archiveMismatch bridgeMismatch noClaim recompute mismatch)

theorem ay_udlb_mismatch_cannot_publish_unsat
    (archiveMismatch : Prop) (bridgeMismatch : Prop)
    (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUDLBBridgeMismatch archiveMismatch bridgeMismatch noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro mismatch
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_udlb_mismatch_no_claim
      archiveMismatch bridgeMismatch noClaim recompute mismatch)
    unsat
