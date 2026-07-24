-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof trimming/replay soundness for ay. Propositions stand for
-- trimmed streams, retained proof steps, dependency coverage, replay order,
-- empty-clause preservation, archive digests, original reconstruction, and
-- no-claim/recompute diagnostics for trimmed-away required dependencies.

def AyUPTRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPTRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPTRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPTRRetainedStep
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) :=
  AyUPTRConj trimmedStream
    (AyUPTRConj retainedStep
      (AyUPTRMap retainedStep dependencyCoverage))

def AyUPTRReplayOrder
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) :=
  AyUPTRConj
    (AyUPTRMap dependencyCoverage orderedReplay)
    (AyUPTRMap orderedReplay emptyClause)

def AyUPTRArchiveDigest
    (trimmedStream : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :=
  AyUPTRConj
    (AyUPTRMap trimmedStream archiveDigest)
    (AyUPTRMap archiveDigest digestAccepted)

def AyUPTRReconstruction
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPTRConj
    (AyUPTRMap emptyClause visibleUnsat)
    (AyUPTRMap visibleUnsat originalUnsat)

def AyUPTRTrimReplayProof
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUPTRConj
    (AyUPTRRetainedStep trimmedStream retainedStep dependencyCoverage)
    (AyUPTRConj
      (AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause)
      (AyUPTRConj
        (AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted)
        (AyUPTRReconstruction emptyClause visibleUnsat originalUnsat)))

def AyUPTRTrimmedDependencyMissing
    (neededDependencyRemoved : Prop) (replayGap : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPTRConj
    (AyUPTRConj noClaim recompute)
    (AyUPTRDisj neededDependencyRemoved replayGap)

def AyUPTRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPTRDisj noClaim originalUnsat

theorem ay_uptr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPTRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uptr_conj_left
    (p : Prop) (q : Prop) :
    AyUPTRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uptr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPTRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uptr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPTRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uptr_retained_dependency
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) :
    AyUPTRRetainedStep trimmedStream retainedStep dependencyCoverage ->
    dependencyCoverage := by
  intro retained
  exact retained dependencyCoverage
    (fun _stream tail =>
      tail dependencyCoverage
        (fun step step_to_dependency => step_to_dependency step))

theorem ay_uptr_replay_ordered
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) :
    AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause ->
    dependencyCoverage ->
    orderedReplay := by
  intro replay
  exact replay (dependencyCoverage -> orderedReplay)
    (fun dependency_to_ordered _ordered_to_empty => dependency_to_ordered)

theorem ay_uptr_replay_empty_clause
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) :
    AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause ->
    orderedReplay ->
    emptyClause := by
  intro replay
  exact replay (orderedReplay -> emptyClause)
    (fun _dependency_to_ordered ordered_to_empty => ordered_to_empty)

theorem ay_uptr_digest_value
    (trimmedStream : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :
    AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted ->
    trimmedStream ->
    archiveDigest := by
  intro digest
  exact digest (trimmedStream -> archiveDigest)
    (fun stream_to_digest _digest_to_accept => stream_to_digest)

theorem ay_uptr_digest_accepted
    (trimmedStream : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) :
    AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted ->
    archiveDigest ->
    digestAccepted := by
  intro digest
  exact digest (archiveDigest -> digestAccepted)
    (fun _stream_to_digest digest_to_accept => digest_to_accept)

theorem ay_uptr_visible_unsat
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRReconstruction emptyClause visibleUnsat originalUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (emptyClause -> visibleUnsat)
    (fun empty_to_visible _visible_to_original => empty_to_visible)

theorem ay_uptr_original_unsat_from_visible
    (emptyClause : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRReconstruction emptyClause visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _empty_to_visible visible_to_original => visible_to_original)

theorem ay_uptr_proof_retained
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUPTRRetainedStep trimmedStream retainedStep dependencyCoverage := by
  intro proof
  exact ay_uptr_conj_left
    (AyUPTRRetainedStep trimmedStream retainedStep dependencyCoverage)
    (AyUPTRConj
      (AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause)
      (AyUPTRConj
        (AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted)
        (AyUPTRReconstruction emptyClause visibleUnsat originalUnsat)))
    proof

theorem ay_uptr_proof_replay
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause := by
  intro proof
  exact proof (AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause)
    (fun _retained tail =>
      tail (AyUPTRReplayOrder dependencyCoverage orderedReplay emptyClause)
        (fun replay _rest => replay))

theorem ay_uptr_proof_digest
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted := by
  intro proof
  exact proof (AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted)
    (fun _retained tail =>
      tail (AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted)
        (fun _replay rest =>
          rest (AyUPTRArchiveDigest trimmedStream archiveDigest digestAccepted)
            (fun digest _reconstruction => digest)))

theorem ay_uptr_proof_reconstruction
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUPTRReconstruction emptyClause visibleUnsat originalUnsat := by
  intro proof
  exact proof (AyUPTRReconstruction emptyClause visibleUnsat originalUnsat)
    (fun _retained tail =>
      tail (AyUPTRReconstruction emptyClause visibleUnsat originalUnsat)
        (fun _replay rest =>
          rest (AyUPTRReconstruction emptyClause visibleUnsat originalUnsat)
            (fun _digest reconstruction => reconstruction)))

theorem ay_uptr_proof_empty_clause
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    emptyClause := by
  intro proof
  exact ay_uptr_replay_empty_clause dependencyCoverage orderedReplay emptyClause
    (ay_uptr_proof_replay trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat proof)
    (ay_uptr_replay_ordered dependencyCoverage orderedReplay emptyClause
      (ay_uptr_proof_replay trimmedStream retainedStep dependencyCoverage
        orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
        originalUnsat proof)
      (ay_uptr_retained_dependency trimmedStream retainedStep dependencyCoverage
        (ay_uptr_proof_retained trimmedStream retainedStep dependencyCoverage
          orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
          originalUnsat proof)))

theorem ay_uptr_trim_replay_original_unsat
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro proof
  exact ay_uptr_original_unsat_from_visible emptyClause visibleUnsat originalUnsat
    (ay_uptr_proof_reconstruction trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat proof)
    (ay_uptr_visible_unsat emptyClause visibleUnsat originalUnsat
      (ay_uptr_proof_reconstruction trimmedStream retainedStep
        dependencyCoverage orderedReplay emptyClause archiveDigest
        digestAccepted visibleUnsat originalUnsat proof)
      (ay_uptr_proof_empty_clause trimmedStream retainedStep dependencyCoverage
        orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
        originalUnsat proof))

theorem ay_uptr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUPTRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uptr_disj_right noClaim originalUnsat unsat

theorem ay_uptr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim ->
    AyUPTRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uptr_disj_left noClaim originalUnsat no_claim

theorem ay_uptr_trim_replay_publish_sound
    (trimmedStream : Prop) (retainedStep : Prop)
    (dependencyCoverage : Prop) (orderedReplay : Prop)
    (emptyClause : Prop) (archiveDigest : Prop)
    (digestAccepted : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUPTRTrimReplayProof trimmedStream retainedStep dependencyCoverage
      orderedReplay emptyClause archiveDigest digestAccepted visibleUnsat
      originalUnsat ->
    AyUPTRPublicReport noClaim originalUnsat := by
  intro proof
  exact ay_uptr_public_unsat_report noClaim originalUnsat
    (ay_uptr_trim_replay_original_unsat trimmedStream retainedStep
      dependencyCoverage orderedReplay emptyClause archiveDigest
      digestAccepted visibleUnsat originalUnsat proof)

theorem ay_uptr_trimmed_dependency_no_claim
    (neededDependencyRemoved : Prop) (replayGap : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPTRTrimmedDependencyMissing
      neededDependencyRemoved replayGap noClaim recompute ->
    noClaim := by
  intro missing
  exact missing noClaim
    (fun both _reason =>
      ay_uptr_conj_left noClaim recompute both)

theorem ay_uptr_trimmed_dependency_recompute
    (neededDependencyRemoved : Prop) (replayGap : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPTRTrimmedDependencyMissing
      neededDependencyRemoved replayGap noClaim recompute ->
    recompute := by
  intro missing
  exact missing recompute
    (fun both _reason =>
      both recompute (fun _no_claim hrecompute => hrecompute))

theorem ay_uptr_trimmed_dependency_public_no_claim
    (neededDependencyRemoved : Prop) (replayGap : Prop)
    (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimmedDependencyMissing
      neededDependencyRemoved replayGap noClaim recompute ->
    AyUPTRPublicReport noClaim originalUnsat := by
  intro missing
  exact ay_uptr_public_no_claim_report noClaim originalUnsat
    (ay_uptr_trimmed_dependency_no_claim
      neededDependencyRemoved replayGap noClaim recompute missing)

theorem ay_uptr_trimmed_dependency_cannot_publish_unsat
    (neededDependencyRemoved : Prop) (replayGap : Prop)
    (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPTRTrimmedDependencyMissing
      neededDependencyRemoved replayGap noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro missing
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_uptr_trimmed_dependency_no_claim
      neededDependencyRemoved replayGap noClaim recompute missing)
    unsat
