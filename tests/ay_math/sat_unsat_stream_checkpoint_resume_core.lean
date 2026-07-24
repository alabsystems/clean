-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Resumable streaming UNSAT proof-checker contract for ay. Propositions stand
-- for compressed chunks, visible chunks, accumulator snapshots, checkpoint
-- records, final empty-clause witnesses, and UNSAT claims. The package proves
-- that resuming from a checked checkpoint reaches the same original-formula
-- UNSAT soundness obligation as checking a full stream from the start.

def AyUSCRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSCRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSCRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSCREquisat (before : Prop) (after : Prop) :=
  AyUSCRConj (before -> after) (after -> before)

def AyUSCRCompressedLookup
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop) :=
  AyUSCRConj archive
    (AyUSCRConj manifest
      (AyUSCRConj
        (AyUSCRMap archive compressedPrefix)
        (AyUSCRMap archive compressedSuffix)))

def AyUSCRChunkProjection
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop) :=
  AyUSCRConj
    (AyUSCRMap compressedPrefix visiblePrefix)
    (AyUSCRMap compressedSuffix visibleSuffix)

def AyUSCRPrefixVerification
    (visiblePrefix : Prop) (initialAccumulator : Prop)
    (checkpointState : Prop) :=
  AyUSCRConj
    (AyUSCRMap visiblePrefix initialAccumulator)
    (AyUSCRMap initialAccumulator checkpointState)

def AyUSCRCheckpointSnapshot
    (checkpointState : Prop) (snapshot : Prop) :=
  AyUSCRConj checkpointState
    (AyUSCRMap checkpointState snapshot)

def AyUSCRSuffixResume
    (snapshot : Prop) (visibleSuffix : Prop)
    (finalAccumulator : Prop) :=
  AyUSCRConj
    (AyUSCRMap snapshot visibleSuffix)
    (AyUSCRMap visibleSuffix finalAccumulator)

def AyUSCRFinalWitness
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :=
  AyUSCRConj
    (AyUSCRMap finalAccumulator emptyClause)
    (AyUSCRMap emptyClause visibleUnsat)

def AyUSCRPreprocessTransport
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCRConj
    (AyUSCREquisat originalCNF visibleCNF)
    (AyUSCRMap visibleUnsat originalUnsat)

def AyUSCRResumeContract
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCRConj
    (AyUSCRCompressedLookup
      archive manifest compressedPrefix compressedSuffix)
    (AyUSCRConj
      (AyUSCRChunkProjection
        compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
      (AyUSCRConj
        (AyUSCRPrefixVerification
          visiblePrefix initialAccumulator checkpointState)
        (AyUSCRConj
          (AyUSCRCheckpointSnapshot checkpointState snapshot)
          (AyUSCRConj
            (AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator)
            (AyUSCRConj
              (AyUSCRFinalWitness
                finalAccumulator emptyClause visibleUnsat)
              (AyUSCRPreprocessTransport
                originalCNF visibleCNF visibleUnsat originalUnsat))))))

def AyUSCRFullStreamContract
    (visibleFullStream : Prop) (initialAccumulator : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSCRConj
    (AyUSCRMap visibleFullStream initialAccumulator)
    (AyUSCRConj
      (AyUSCRMap initialAccumulator finalAccumulator)
      (AyUSCRConj
        (AyUSCRMap finalAccumulator emptyClause)
        (AyUSCRConj
          (AyUSCRMap emptyClause visibleUnsat)
          (AyUSCRMap visibleUnsat originalUnsat))))

theorem ay_uscr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSCRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uscr_conj_left
    (p : Prop) (q : Prop) :
    AyUSCRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uscr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSCRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uscr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSCRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uscr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSCREquisat before after := by
  intro forward
  intro backward
  exact ay_uscr_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_uscr_equisat_forward
    (before : Prop) (after : Prop) :
    AyUSCREquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_uscr_equisat_backward
    (before : Prop) (after : Prop) :
    AyUSCREquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_uscr_lookup_prefix
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop) :
    AyUSCRCompressedLookup
      archive manifest compressedPrefix compressedSuffix ->
    compressedPrefix := by
  intro lookup
  exact lookup compressedPrefix
    (fun harchive tail =>
      tail compressedPrefix
        (fun _manifest maps =>
          maps compressedPrefix
            (fun archive_to_prefix _archive_to_suffix =>
              archive_to_prefix harchive)))

theorem ay_uscr_lookup_suffix
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop) :
    AyUSCRCompressedLookup
      archive manifest compressedPrefix compressedSuffix ->
    compressedSuffix := by
  intro lookup
  exact lookup compressedSuffix
    (fun harchive tail =>
      tail compressedSuffix
        (fun _manifest maps =>
          maps compressedSuffix
            (fun _archive_to_prefix archive_to_suffix =>
              archive_to_suffix harchive)))

theorem ay_uscr_project_visible_prefix
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop) :
    AyUSCRChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix ->
    compressedPrefix ->
    visiblePrefix := by
  intro projection
  exact projection (compressedPrefix -> visiblePrefix)
    (fun prefix_map _suffix_map => prefix_map)

theorem ay_uscr_project_visible_suffix
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop) :
    AyUSCRChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix ->
    compressedSuffix ->
    visibleSuffix := by
  intro projection
  exact projection (compressedSuffix -> visibleSuffix)
    (fun _prefix_map suffix_map => suffix_map)

theorem ay_uscr_prefix_initial
    (visiblePrefix : Prop) (initialAccumulator : Prop)
    (checkpointState : Prop) :
    AyUSCRPrefixVerification
      visiblePrefix initialAccumulator checkpointState ->
    visiblePrefix ->
    initialAccumulator := by
  intro verification
  exact verification (visiblePrefix -> initialAccumulator)
    (fun prefix_to_initial _initial_to_checkpoint => prefix_to_initial)

theorem ay_uscr_prefix_checkpoint
    (visiblePrefix : Prop) (initialAccumulator : Prop)
    (checkpointState : Prop) :
    AyUSCRPrefixVerification
      visiblePrefix initialAccumulator checkpointState ->
    initialAccumulator ->
    checkpointState := by
  intro verification
  exact verification (initialAccumulator -> checkpointState)
    (fun _prefix_to_initial initial_to_checkpoint =>
      initial_to_checkpoint)

theorem ay_uscr_prefix_checkpoint_from_visible
    (visiblePrefix : Prop) (initialAccumulator : Prop)
    (checkpointState : Prop) :
    AyUSCRPrefixVerification
      visiblePrefix initialAccumulator checkpointState ->
    visiblePrefix ->
    checkpointState := by
  intro verification
  intro hprefix
  exact ay_uscr_prefix_checkpoint
    visiblePrefix initialAccumulator checkpointState verification
    (ay_uscr_prefix_initial
      visiblePrefix initialAccumulator checkpointState verification hprefix)

theorem ay_uscr_snapshot_from_checkpoint
    (checkpointState : Prop) (snapshot : Prop) :
    AyUSCRCheckpointSnapshot checkpointState snapshot ->
    snapshot := by
  intro checkpoint
  exact checkpoint snapshot
    (fun hcheckpoint checkpoint_to_snapshot =>
      checkpoint_to_snapshot hcheckpoint)

theorem ay_uscr_resume_visible_suffix
    (snapshot : Prop) (visibleSuffix : Prop)
    (finalAccumulator : Prop) :
    AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator ->
    snapshot ->
    visibleSuffix := by
  intro resume_cert
  exact resume_cert (snapshot -> visibleSuffix)
    (fun snapshot_to_suffix _suffix_to_final => snapshot_to_suffix)

theorem ay_uscr_resume_final
    (snapshot : Prop) (visibleSuffix : Prop)
    (finalAccumulator : Prop) :
    AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator ->
    visibleSuffix ->
    finalAccumulator := by
  intro resume_cert
  exact resume_cert (visibleSuffix -> finalAccumulator)
    (fun _snapshot_to_suffix suffix_to_final => suffix_to_final)

theorem ay_uscr_resume_final_from_snapshot
    (snapshot : Prop) (visibleSuffix : Prop)
    (finalAccumulator : Prop) :
    AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator ->
    snapshot ->
    finalAccumulator := by
  intro resume_cert
  intro hsnapshot
  exact ay_uscr_resume_final snapshot visibleSuffix finalAccumulator
    resume_cert
    (ay_uscr_resume_visible_suffix
      snapshot visibleSuffix finalAccumulator resume_cert hsnapshot)

theorem ay_uscr_empty_from_final
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    emptyClause := by
  intro witness
  exact witness (finalAccumulator -> emptyClause)
    (fun final_to_empty _empty_to_unsat => final_to_empty)

theorem ay_uscr_visible_unsat_from_empty
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat ->
    emptyClause ->
    visibleUnsat := by
  intro witness
  exact witness (emptyClause -> visibleUnsat)
    (fun _final_to_empty empty_to_unsat => empty_to_unsat)

theorem ay_uscr_visible_unsat_from_final
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) :
    AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat ->
    finalAccumulator ->
    visibleUnsat := by
  intro witness
  intro hfinal
  exact ay_uscr_visible_unsat_from_empty
    finalAccumulator emptyClause visibleUnsat witness
    (ay_uscr_empty_from_final
      finalAccumulator emptyClause visibleUnsat witness hfinal)

theorem ay_uscr_preprocess_transport_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro transport
  exact transport (visibleUnsat -> originalUnsat)
    (fun _equisat visible_to_original => visible_to_original)

theorem ay_uscr_resume_lookup
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRCompressedLookup
      archive manifest compressedPrefix compressedSuffix := by
  intro contract
  exact ay_uscr_conj_left
    (AyUSCRCompressedLookup
      archive manifest compressedPrefix compressedSuffix)
    (AyUSCRConj
      (AyUSCRChunkProjection
        compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
      (AyUSCRConj
        (AyUSCRPrefixVerification
          visiblePrefix initialAccumulator checkpointState)
        (AyUSCRConj
          (AyUSCRCheckpointSnapshot checkpointState snapshot)
          (AyUSCRConj
            (AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator)
            (AyUSCRConj
              (AyUSCRFinalWitness
                finalAccumulator emptyClause visibleUnsat)
              (AyUSCRPreprocessTransport
                originalCNF visibleCNF visibleUnsat originalUnsat))))))
    contract

theorem ay_uscr_resume_projection
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix := by
  intro contract
  exact contract
    (AyUSCRChunkProjection
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
    (fun _lookup tail =>
      tail
        (AyUSCRChunkProjection
          compressedPrefix compressedSuffix visiblePrefix visibleSuffix)
        (fun projection _rest => projection))

theorem ay_uscr_resume_checkpoint
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRCheckpointSnapshot checkpointState snapshot := by
  intro contract
  exact contract
    (AyUSCRCheckpointSnapshot checkpointState snapshot)
    (fun _lookup tail =>
      tail (AyUSCRCheckpointSnapshot checkpointState snapshot)
        (fun _projection rest =>
          rest (AyUSCRCheckpointSnapshot checkpointState snapshot)
            (fun _prefix tail2 =>
              tail2 (AyUSCRCheckpointSnapshot checkpointState snapshot)
                (fun checkpoint _tail => checkpoint))))

theorem ay_uscr_resume_suffix
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator := by
  intro contract
  exact contract (AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator)
    (fun _lookup tail =>
      tail (AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator)
        (fun _projection rest =>
          rest (AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator)
            (fun _prefix tail2 =>
              tail2 (AyUSCRSuffixResume snapshot visibleSuffix finalAccumulator)
                (fun _checkpoint tail3 =>
                  tail3
                    (AyUSCRSuffixResume
                      snapshot visibleSuffix finalAccumulator)
                    (fun suffix _tail => suffix))))))

theorem ay_uscr_resume_final_witness
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat := by
  intro contract
  exact contract (AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat)
    (fun _lookup tail =>
      tail (AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat)
        (fun _projection rest =>
          rest (AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat)
            (fun _prefix tail2 =>
              tail2 (AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat)
                (fun _checkpoint tail3 =>
                  tail3
                    (AyUSCRFinalWitness finalAccumulator emptyClause visibleUnsat)
                    (fun _suffix tail4 =>
                      tail4
                        (AyUSCRFinalWitness
                          finalAccumulator emptyClause visibleUnsat)
                        (fun witness _transport => witness)))))))

theorem ay_uscr_resume_preprocess
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSCRPreprocessTransport
      originalCNF visibleCNF visibleUnsat originalUnsat)
    (fun _lookup tail =>
      tail
        (AyUSCRPreprocessTransport
          originalCNF visibleCNF visibleUnsat originalUnsat)
        (fun _projection rest =>
          rest
            (AyUSCRPreprocessTransport
              originalCNF visibleCNF visibleUnsat originalUnsat)
            (fun _prefix tail2 =>
              tail2
                (AyUSCRPreprocessTransport
                  originalCNF visibleCNF visibleUnsat originalUnsat)
                (fun _checkpoint tail3 =>
                  tail3
                    (AyUSCRPreprocessTransport
                      originalCNF visibleCNF visibleUnsat originalUnsat)
                    (fun _suffix tail4 =>
                      tail4
                        (AyUSCRPreprocessTransport
                          originalCNF visibleCNF visibleUnsat originalUnsat)
                        (fun _witness transport => transport)))))))

theorem ay_uscr_resume_visible_prefix
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    visiblePrefix := by
  intro contract
  exact ay_uscr_project_visible_prefix
    compressedPrefix compressedSuffix visiblePrefix visibleSuffix
    (ay_uscr_resume_projection
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)
    (ay_uscr_lookup_prefix archive manifest compressedPrefix compressedSuffix
      (ay_uscr_resume_lookup
        originalCNF visibleCNF archive manifest compressedPrefix
        compressedSuffix visiblePrefix visibleSuffix initialAccumulator
        checkpointState snapshot finalAccumulator emptyClause visibleUnsat
        originalUnsat contract))

theorem ay_uscr_resume_snapshot
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    snapshot := by
  intro contract
  exact ay_uscr_snapshot_from_checkpoint checkpointState snapshot
    (ay_uscr_resume_checkpoint
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)

theorem ay_uscr_resume_final_accumulator
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    finalAccumulator := by
  intro contract
  exact ay_uscr_resume_final_from_snapshot
    snapshot visibleSuffix finalAccumulator
    (ay_uscr_resume_suffix
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)
    (ay_uscr_resume_snapshot
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)

theorem ay_uscr_resume_visible_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    visibleUnsat := by
  intro contract
  exact ay_uscr_visible_unsat_from_final
    finalAccumulator emptyClause visibleUnsat
    (ay_uscr_resume_final_witness
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)
    (ay_uscr_resume_final_accumulator
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)

theorem ay_uscr_resume_original_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_uscr_preprocess_transport_unsat
    originalCNF visibleCNF visibleUnsat originalUnsat
    (ay_uscr_resume_preprocess
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)
    (ay_uscr_resume_visible_unsat
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)

theorem ay_uscr_full_original_unsat
    (visibleFullStream : Prop) (initialAccumulator : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRFullStreamContract visibleFullStream initialAccumulator
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    visibleFullStream ->
    originalUnsat := by
  intro full
  intro hstream
  exact full originalUnsat
    (fun stream_to_initial tail =>
      tail originalUnsat
        (fun initial_to_final tail2 =>
          tail2 originalUnsat
            (fun final_to_empty tail3 =>
              tail3 originalUnsat
                (fun empty_to_unsat unsat_to_original =>
                  unsat_to_original
                    (empty_to_unsat
                      (final_to_empty
                        (initial_to_final
                          (stream_to_initial hstream))))))))

theorem ay_uscr_resume_to_full_stream_contract
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    AyUSCRFullStreamContract snapshot snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat := by
  intro contract
  exact ay_uscr_conj_intro
    (snapshot -> snapshot)
    (AyUSCRConj
      (snapshot -> finalAccumulator)
      (AyUSCRConj
        (finalAccumulator -> emptyClause)
        (AyUSCRConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat))))
    (fun hsnapshot => hsnapshot)
    (ay_uscr_conj_intro
      (snapshot -> finalAccumulator)
      (AyUSCRConj
        (finalAccumulator -> emptyClause)
        (AyUSCRConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat)))
      (fun hsnapshot =>
        ay_uscr_resume_final_from_snapshot snapshot visibleSuffix
          finalAccumulator
          (ay_uscr_resume_suffix
            originalCNF visibleCNF archive manifest compressedPrefix
            compressedSuffix visiblePrefix visibleSuffix initialAccumulator
            checkpointState snapshot finalAccumulator emptyClause visibleUnsat
            originalUnsat contract)
          hsnapshot)
      (ay_uscr_conj_intro
        (finalAccumulator -> emptyClause)
        (AyUSCRConj
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat))
        (ay_uscr_empty_from_final finalAccumulator emptyClause visibleUnsat
          (ay_uscr_resume_final_witness
            originalCNF visibleCNF archive manifest compressedPrefix
            compressedSuffix visiblePrefix visibleSuffix initialAccumulator
            checkpointState snapshot finalAccumulator emptyClause visibleUnsat
            originalUnsat contract))
        (ay_uscr_conj_intro
          (emptyClause -> visibleUnsat)
          (visibleUnsat -> originalUnsat)
          (ay_uscr_visible_unsat_from_empty
            finalAccumulator emptyClause visibleUnsat
            (ay_uscr_resume_final_witness
              originalCNF visibleCNF archive manifest compressedPrefix
              compressedSuffix visiblePrefix visibleSuffix initialAccumulator
              checkpointState snapshot finalAccumulator emptyClause
              visibleUnsat originalUnsat contract))
          (ay_uscr_preprocess_transport_unsat
            originalCNF visibleCNF visibleUnsat originalUnsat
            (ay_uscr_resume_preprocess
              originalCNF visibleCNF archive manifest compressedPrefix
              compressedSuffix visiblePrefix visibleSuffix initialAccumulator
              checkpointState snapshot finalAccumulator emptyClause
              visibleUnsat originalUnsat contract)))))

theorem ay_uscr_checkpoint_resume_equiv_full_unsat
    (originalCNF : Prop) (visibleCNF : Prop)
    (archive : Prop) (manifest : Prop)
    (compressedPrefix : Prop) (compressedSuffix : Prop)
    (visiblePrefix : Prop) (visibleSuffix : Prop)
    (initialAccumulator : Prop) (checkpointState : Prop)
    (snapshot : Prop) (finalAccumulator : Prop)
    (emptyClause : Prop) (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSCRResumeContract originalCNF visibleCNF archive manifest
      compressedPrefix compressedSuffix visiblePrefix visibleSuffix
      initialAccumulator checkpointState snapshot finalAccumulator
      emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro contract
  exact ay_uscr_full_original_unsat
    snapshot snapshot finalAccumulator emptyClause
    visibleUnsat originalUnsat
    (ay_uscr_resume_to_full_stream_contract
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)
    (ay_uscr_resume_snapshot
      originalCNF visibleCNF archive manifest compressedPrefix compressedSuffix
      visiblePrefix visibleSuffix initialAccumulator checkpointState snapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat contract)
