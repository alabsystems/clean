-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof-shard rehydration contract for ay. Propositions stand for
-- archived shards, membership proofs, Merkle digest/root agreement, clause
-- dependencies, empty-clause witnesses, original-formula reconstruction, and
-- no-claim/recompute diagnostics for unavailable shards.

def AyUPSRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPSRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPSRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPSRMembership
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) :=
  AyUPSRConj archivedShard
    (AyUPSRConj membershipProof
      (AyUPSRMap archivedShard rehydratedShard))

def AyUPSRMerkleAgreement
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) :=
  AyUPSRConj
    (AyUPSRMap rehydratedShard shardDigest)
    (AyUPSRMap shardDigest merkleRoot)

def AyUPSRClauseDependency
    (rehydratedShard : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) :=
  AyUPSRConj
    (AyUPSRMap rehydratedShard dependencyChain)
    (AyUPSRMap dependencyChain emptyClause)

def AyUPSRReconstructionChain
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPSRConj
    (AyUPSRMap emptyClause visibleUnsat)
    (AyUPSRMap visibleUnsat originalUnsat)

def AyUPSRRehydratedProof
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPSRConj
    (AyUPSRMembership archivedShard membershipProof rehydratedShard)
    (AyUPSRConj
      (AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot)
      (AyUPSRConj
        (AyUPSRClauseDependency
          rehydratedShard dependencyChain emptyClause)
        (AyUPSRReconstructionChain
          emptyClause visibleUnsat originalUnsat)))

def AyUPSRUnavailableShard
    (missingShard : Prop) (corruptShard : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPSRConj
    (AyUPSRConj noClaim recompute)
    (AyUPSRDisj missingShard corruptShard)

def AyUPSRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPSRDisj noClaim originalUnsat

theorem ay_upsr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPSRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upsr_conj_left
    (p : Prop) (q : Prop) :
    AyUPSRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upsr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPSRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upsr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPSRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upsr_membership_shard
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) :
    AyUPSRMembership archivedShard membershipProof rehydratedShard ->
    rehydratedShard := by
  intro membership
  exact membership rehydratedShard
    (fun archived tail =>
      tail rehydratedShard
        (fun _proof archive_to_shard => archive_to_shard archived))

theorem ay_upsr_merkle_digest
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) :
    AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot ->
    rehydratedShard ->
    shardDigest := by
  intro agreement
  exact agreement (rehydratedShard -> shardDigest)
    (fun shard_to_digest _digest_to_root => shard_to_digest)

theorem ay_upsr_merkle_root
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) :
    AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot ->
    shardDigest ->
    merkleRoot := by
  intro agreement
  exact agreement (shardDigest -> merkleRoot)
    (fun _shard_to_digest digest_to_root => digest_to_root)

theorem ay_upsr_dependency_chain
    (rehydratedShard : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) :
    AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause ->
    rehydratedShard ->
    dependencyChain := by
  intro dependency
  exact dependency (rehydratedShard -> dependencyChain)
    (fun shard_to_dependency _dependency_to_empty => shard_to_dependency)

theorem ay_upsr_dependency_empty_clause
    (rehydratedShard : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) :
    AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause ->
    dependencyChain ->
    emptyClause := by
  intro dependency
  exact dependency (dependencyChain -> emptyClause)
    (fun _shard_to_dependency dependency_to_empty => dependency_to_empty)

theorem ay_upsr_reconstruct_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_upsr_reconstruct_original_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_upsr_rehydrated_membership
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    AyUPSRMembership archivedShard membershipProof rehydratedShard := by
  intro proof
  exact ay_upsr_conj_left
    (AyUPSRMembership archivedShard membershipProof rehydratedShard)
    (AyUPSRConj
      (AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot)
      (AyUPSRConj
        (AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause)
        (AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat)))
    proof

theorem ay_upsr_rehydrated_merkle
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot := by
  intro proof
  exact proof (AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot)
    (fun _membership tail =>
      tail (AyUPSRMerkleAgreement rehydratedShard shardDigest merkleRoot)
        (fun merkle _rest => merkle))

theorem ay_upsr_rehydrated_dependency
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause := by
  intro proof
  exact proof
    (AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause)
    (fun _membership tail =>
      tail
        (AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause)
        (fun _merkle rest =>
          rest (AyUPSRClauseDependency rehydratedShard dependencyChain emptyClause)
            (fun dependency _reconstruction => dependency)))

theorem ay_upsr_rehydrated_reconstruction
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof
    (AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat)
    (fun _membership tail =>
      tail
        (AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat)
        (fun _merkle rest =>
          rest
            (AyUPSRReconstructionChain emptyClause visibleUnsat originalUnsat)
            (fun _dependency reconstruction => reconstruction)))

theorem ay_upsr_rehydrated_empty_clause
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro proof
  exact ay_upsr_dependency_empty_clause rehydratedShard dependencyChain emptyClause
    (ay_upsr_rehydrated_dependency archivedShard membershipProof
      rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
      visibleUnsat originalUnsat proof)
    (ay_upsr_dependency_chain rehydratedShard dependencyChain emptyClause
      (ay_upsr_rehydrated_dependency archivedShard membershipProof
        rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
        visibleUnsat originalUnsat proof)
      (ay_upsr_membership_shard archivedShard membershipProof rehydratedShard
        (ay_upsr_rehydrated_membership archivedShard membershipProof
          rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
          visibleUnsat originalUnsat proof)))

theorem ay_upsr_rehydration_original_unsat
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro proof
  exact ay_upsr_reconstruct_original_unsat emptyClause visibleUnsat originalUnsat
    (ay_upsr_rehydrated_reconstruction archivedShard membershipProof
      rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
      visibleUnsat originalUnsat proof)
    (ay_upsr_reconstruct_visible_unsat emptyClause visibleUnsat originalUnsat
      (ay_upsr_rehydrated_reconstruction archivedShard membershipProof
        rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
        visibleUnsat originalUnsat proof)
      (ay_upsr_rehydrated_empty_clause archivedShard membershipProof
        rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
        visibleUnsat originalUnsat proof))

theorem ay_upsr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUPSRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upsr_disj_right noClaim originalUnsat unsat

theorem ay_upsr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUPSRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upsr_disj_left noClaim originalUnsat no_claim

theorem ay_upsr_rehydration_publish_sound
    (archivedShard : Prop) (membershipProof : Prop)
    (rehydratedShard : Prop) (shardDigest : Prop)
    (merkleRoot : Prop) (dependencyChain : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUPSRRehydratedProof archivedShard membershipProof rehydratedShard
      shardDigest merkleRoot dependencyChain emptyClause visibleUnsat
      originalUnsat ->
    AyUPSRPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_upsr_public_unsat_report noClaim originalUnsat
    (ay_upsr_rehydration_original_unsat archivedShard membershipProof
      rehydratedShard shardDigest merkleRoot dependencyChain emptyClause
      visibleUnsat originalUnsat proof)

theorem ay_upsr_unavailable_no_claim
    (missingShard : Prop) (corruptShard : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPSRUnavailableShard missingShard corruptShard noClaim recompute ->
    noClaim := by
  intro unavailable
  exact unavailable noClaim
    (fun both _missing_or_corrupt =>
      ay_upsr_conj_left noClaim recompute both)

theorem ay_upsr_unavailable_recompute
    (missingShard : Prop) (corruptShard : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPSRUnavailableShard missingShard corruptShard noClaim recompute ->
    recompute := by
  intro unavailable
  exact unavailable recompute
    (fun both _missing_or_corrupt =>
      both recompute (fun _no_claim hrecompute => hrecompute))

theorem ay_upsr_unavailable_public_no_claim
    (missingShard : Prop) (corruptShard : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPSRUnavailableShard missingShard corruptShard noClaim recompute ->
    AyUPSRPublicReport noClaim originalUnsat := by
  intro unavailable
  exact ay_upsr_public_no_claim_report noClaim originalUnsat
    (ay_upsr_unavailable_no_claim
      missingShard corruptShard noClaim recompute unavailable)

theorem ay_upsr_unavailable_cannot_publish_unsat
    (missingShard : Prop) (corruptShard : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPSRUnavailableShard missingShard corruptShard noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro unavailable
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_upsr_unavailable_no_claim
      missingShard corruptShard noClaim recompute unavailable)
    unsat
