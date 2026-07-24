-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Artifact-index algebra for compressed UNSAT replay certificates after
-- preprocessing. Propositions stand for the artifact index, lookup result,
-- replay artifact, empty-clause witness, formulas, and UNSAT claims. All API
-- surfaces are compact Church-encoded maps/certificates.

def AyUAICConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUAICDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUAICMap (source : Prop) (target : Prop) :=
  source -> target

def AyUAICEquisat (before : Prop) (after : Prop) :=
  AyUAICConj (before -> after) (after -> before)

def AyUAICLookupAPI
    (artifactIndex : Prop) (lookupKey : Prop) (lookupResult : Prop) :=
  AyUAICConj artifactIndex
    (AyUAICConj lookupKey
      (AyUAICMap artifactIndex lookupResult))

def AyUAICProjectionAPI
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop) :=
  AyUAICConj
    (AyUAICMap lookupResult replayArtifact)
    (AyUAICMap replayArtifact emptyWitness)

def AyUAICReconstructionAPI
    (emptyWitness : Prop) (preprocessedUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUAICConj
    (AyUAICMap emptyWitness preprocessedUnsat)
    (AyUAICMap preprocessedUnsat originalUnsat)

def AyUAICIndexedCompressedUnsat
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :=
  AyUAICConj
    (AyUAICEquisat original preprocessed)
    (AyUAICConj
      (AyUAICLookupAPI artifactIndex lookupKey lookupResult)
      (AyUAICConj
        (AyUAICProjectionAPI lookupResult replayArtifact emptyWitness)
        (AyUAICReconstructionAPI
          emptyWitness preprocessedUnsat originalUnsat)))

theorem ay_uaic_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUAICConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uaic_conj_left
    (p : Prop) (q : Prop) :
    AyUAICConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uaic_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUAICDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uaic_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUAICDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uaic_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUAICEquisat before after := by
  intro forward
  intro backward
  exact ay_uaic_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_uaic_equisat_forward
    (before : Prop) (after : Prop) :
    AyUAICEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_uaic_equisat_backward
    (before : Prop) (after : Prop) :
    AyUAICEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_uaic_lookup_index
    (artifactIndex : Prop) (lookupKey : Prop) (lookupResult : Prop) :
    AyUAICLookupAPI artifactIndex lookupKey lookupResult ->
    artifactIndex := by
  intro lookup
  exact ay_uaic_conj_left artifactIndex
    (AyUAICConj lookupKey
      (AyUAICMap artifactIndex lookupResult))
    lookup

theorem ay_uaic_lookup_key
    (artifactIndex : Prop) (lookupKey : Prop) (lookupResult : Prop) :
    AyUAICLookupAPI artifactIndex lookupKey lookupResult ->
    lookupKey := by
  intro lookup
  exact lookup lookupKey
    (fun _index tail =>
      tail lookupKey
        (fun key _lookup_map => key))

theorem ay_uaic_lookup_result
    (artifactIndex : Prop) (lookupKey : Prop) (lookupResult : Prop) :
    AyUAICLookupAPI artifactIndex lookupKey lookupResult ->
    lookupResult := by
  intro lookup
  exact lookup lookupResult
    (fun index tail =>
      tail lookupResult
        (fun _key lookup_map => lookup_map index))

theorem ay_uaic_projection_replay_artifact
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop) :
    AyUAICProjectionAPI lookupResult replayArtifact emptyWitness ->
    lookupResult ->
    replayArtifact := by
  intro projection
  exact projection (lookupResult -> replayArtifact)
    (fun lookup_to_replay _replay_to_empty => lookup_to_replay)

theorem ay_uaic_projection_empty_witness
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop) :
    AyUAICProjectionAPI lookupResult replayArtifact emptyWitness ->
    replayArtifact ->
    emptyWitness := by
  intro projection
  exact projection (replayArtifact -> emptyWitness)
    (fun _lookup_to_replay replay_to_empty => replay_to_empty)

theorem ay_uaic_projection_empty_from_lookup
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop) :
    AyUAICProjectionAPI lookupResult replayArtifact emptyWitness ->
    lookupResult ->
    emptyWitness := by
  intro projection
  intro hlookup
  exact ay_uaic_projection_empty_witness
    lookupResult replayArtifact emptyWitness projection
    (ay_uaic_projection_replay_artifact
      lookupResult replayArtifact emptyWitness projection hlookup)

theorem ay_uaic_reconstruct_preprocessed_unsat
    (emptyWitness : Prop) (preprocessedUnsat : Prop)
    (originalUnsat : Prop) :
    AyUAICReconstructionAPI emptyWitness preprocessedUnsat originalUnsat ->
    emptyWitness ->
    preprocessedUnsat := by
  intro reconstruct
  exact reconstruct (emptyWitness -> preprocessedUnsat)
    (fun empty_to_preprocessed _preprocessed_to_original =>
      empty_to_preprocessed)

theorem ay_uaic_reconstruct_original_unsat
    (emptyWitness : Prop) (preprocessedUnsat : Prop)
    (originalUnsat : Prop) :
    AyUAICReconstructionAPI emptyWitness preprocessedUnsat originalUnsat ->
    preprocessedUnsat ->
    originalUnsat := by
  intro reconstruct
  exact reconstruct (preprocessedUnsat -> originalUnsat)
    (fun _empty_to_preprocessed preprocessed_to_original =>
      preprocessed_to_original)

theorem ay_uaic_reconstruct_original_from_empty
    (emptyWitness : Prop) (preprocessedUnsat : Prop)
    (originalUnsat : Prop) :
    AyUAICReconstructionAPI emptyWitness preprocessedUnsat originalUnsat ->
    emptyWitness ->
    originalUnsat := by
  intro reconstruct
  intro hempty
  exact ay_uaic_reconstruct_original_unsat
    emptyWitness preprocessedUnsat originalUnsat reconstruct
    (ay_uaic_reconstruct_preprocessed_unsat
      emptyWitness preprocessedUnsat originalUnsat reconstruct hempty)

theorem ay_uaic_indexed_equisat
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    AyUAICEquisat original preprocessed := by
  intro cert
  exact ay_uaic_conj_left
    (AyUAICEquisat original preprocessed)
    (AyUAICConj
      (AyUAICLookupAPI artifactIndex lookupKey lookupResult)
      (AyUAICConj
        (AyUAICProjectionAPI lookupResult replayArtifact emptyWitness)
        (AyUAICReconstructionAPI
          emptyWitness preprocessedUnsat originalUnsat)))
    cert

theorem ay_uaic_indexed_lookup
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    AyUAICLookupAPI artifactIndex lookupKey lookupResult := by
  intro cert
  exact cert (AyUAICLookupAPI artifactIndex lookupKey lookupResult)
    (fun _equisat tail =>
      tail (AyUAICLookupAPI artifactIndex lookupKey lookupResult)
        (fun lookup _rest => lookup))

theorem ay_uaic_indexed_projection
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    AyUAICProjectionAPI lookupResult replayArtifact emptyWitness := by
  intro cert
  exact cert (AyUAICProjectionAPI lookupResult replayArtifact emptyWitness)
    (fun _equisat tail =>
      tail (AyUAICProjectionAPI lookupResult replayArtifact emptyWitness)
        (fun _lookup rest =>
          rest (AyUAICProjectionAPI lookupResult replayArtifact emptyWitness)
            (fun projection _reconstruction => projection)))

theorem ay_uaic_indexed_reconstruction
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    AyUAICReconstructionAPI emptyWitness preprocessedUnsat originalUnsat := by
  intro cert
  exact cert
    (AyUAICReconstructionAPI emptyWitness preprocessedUnsat originalUnsat)
    (fun _equisat tail =>
      tail
        (AyUAICReconstructionAPI emptyWitness preprocessedUnsat originalUnsat)
        (fun _lookup rest =>
          rest
            (AyUAICReconstructionAPI
              emptyWitness preprocessedUnsat originalUnsat)
            (fun _projection reconstruction => reconstruction)))

theorem ay_uaic_indexed_lookup_empty_witness
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    emptyWitness := by
  intro cert
  exact ay_uaic_projection_empty_from_lookup
    lookupResult replayArtifact emptyWitness
    (ay_uaic_indexed_projection
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)
    (ay_uaic_lookup_result artifactIndex lookupKey lookupResult
      (ay_uaic_indexed_lookup
        original preprocessed artifactIndex lookupKey lookupResult
        replayArtifact emptyWitness preprocessedUnsat originalUnsat cert))

theorem ay_uaic_indexed_lookup_preprocessed_unsat
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    preprocessedUnsat := by
  intro cert
  exact ay_uaic_reconstruct_preprocessed_unsat
    emptyWitness preprocessedUnsat originalUnsat
    (ay_uaic_indexed_reconstruction
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)
    (ay_uaic_indexed_lookup_empty_witness
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)

theorem ay_uaic_indexed_lookup_original_unsat
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    originalUnsat := by
  intro cert
  exact ay_uaic_reconstruct_original_unsat
    emptyWitness preprocessedUnsat originalUnsat
    (ay_uaic_indexed_reconstruction
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)
    (ay_uaic_indexed_lookup_preprocessed_unsat
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)

theorem ay_uaic_preprocessing_roundtrip_to_preprocessed
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    original ->
    preprocessed := by
  intro cert
  exact ay_uaic_equisat_forward original preprocessed
    (ay_uaic_indexed_equisat
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)

theorem ay_uaic_preprocessing_roundtrip_to_original
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    preprocessed ->
    original := by
  intro cert
  exact ay_uaic_equisat_backward original preprocessed
    (ay_uaic_indexed_equisat
      original preprocessed artifactIndex lookupKey lookupResult replayArtifact
      emptyWitness preprocessedUnsat originalUnsat cert)

theorem ay_uaic_indexed_compressed_artifact_lookup_sound
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    originalUnsat := by
  intro cert
  exact ay_uaic_indexed_lookup_original_unsat
    original preprocessed artifactIndex lookupKey lookupResult replayArtifact
    emptyWitness preprocessedUnsat originalUnsat cert

theorem ay_uaic_indexed_compressed_unsat_under_roundtrip
    (original : Prop) (preprocessed : Prop)
    (artifactIndex : Prop) (lookupKey : Prop)
    (lookupResult : Prop) (replayArtifact : Prop)
    (emptyWitness : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyUAICIndexedCompressedUnsat original preprocessed artifactIndex
      lookupKey lookupResult replayArtifact emptyWitness
      preprocessedUnsat originalUnsat ->
    original ->
    originalUnsat := by
  intro cert
  intro _horiginal
  exact ay_uaic_indexed_compressed_artifact_lookup_sound
    original preprocessed artifactIndex lookupKey lookupResult replayArtifact
    emptyWitness preprocessedUnsat originalUnsat cert
