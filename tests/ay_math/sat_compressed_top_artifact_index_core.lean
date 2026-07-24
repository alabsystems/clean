-- SAT-COMP compressed top artifact-index core.
--
-- This package models the artifact layer that sits above a compressed
-- top-level SAT-COMP outcome.  An index can look up a compressed outcome,
-- project it to visible SAT or replay UNSAT artifacts, and reconstruct the
-- compressed certificate without changing the top-level soundness statement.

def AyAICConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyAICDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAICEquisat (before after : Prop) : Prop :=
  AyAICConj (before -> after) (after -> before)

def AyAICOutcome (sat unsat : Prop) : Prop :=
  AyAICDisj sat unsat

def AyAICCompressed (payload : Prop) : Prop :=
  payload

def AyAICIndexed (index payload : Prop) : Prop :=
  AyAICConj index payload

def AyAICLookup (index payload : Prop) : Prop :=
  index -> payload

def AyAICProjection (payload visibleSat replayUnsat : Prop) : Prop :=
  payload -> AyAICOutcome visibleSat replayUnsat

def AyAICReconstruction (visibleSat replayUnsat payload : Prop) : Prop :=
  AyAICOutcome visibleSat replayUnsat -> payload

def AyAICModel (formula assignment : Prop) : Prop :=
  AyAICConj formula assignment

def AyAICUnsat (formula : Prop) : Prop :=
  formula -> False

def AyAICReplayCert (formula stream finalClause : Prop) : Prop :=
  stream -> formula -> finalClause

def AyAICCDCLSat (solver internalAssignment : Prop) : Prop :=
  AyAICModel solver internalAssignment

def AyAICCDCLUnsat (stream : Prop) : Prop :=
  stream

def AyAICVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyAICModel original visibleAssignment

theorem ay_aic_conj_intro (left right : Prop) :
    left -> right -> AyAICConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_aic_conj_left (left right : Prop) :
    AyAICConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_aic_conj_right (left right : Prop) :
    AyAICConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_aic_disj_left (left right : Prop) :
    left -> AyAICDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_aic_disj_right (left right : Prop) :
    right -> AyAICDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_aic_equisat_forward (before after : Prop) :
    AyAICEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_aic_equisat_backward (before after : Prop) :
    AyAICEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_aic_equisat_refl (payload : Prop) :
    AyAICEquisat payload payload :=
  ay_aic_conj_intro (payload -> payload) (payload -> payload)
    (fun h => h) (fun h => h)

theorem ay_aic_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyAICModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_aic_conj_intro formula assignment formulaProof assignmentProof

theorem ay_aic_model_formula (formula assignment : Prop) :
    AyAICModel formula assignment -> formula :=
  fun model => ay_aic_conj_left formula assignment model

theorem ay_aic_model_assignment (formula assignment : Prop) :
    AyAICModel formula assignment -> assignment :=
  fun model => ay_aic_conj_right formula assignment model

theorem ay_aic_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyAICOutcome beforeSat beforeUnsat ->
    AyAICOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_aic_outcome_roundtrip
    (leftSat rightSat leftUnsat rightUnsat : Prop) :
    (leftSat -> rightSat) ->
    (rightSat -> leftSat) ->
    (leftUnsat -> rightUnsat) ->
    (rightUnsat -> leftUnsat) ->
    AyAICEquisat
      (AyAICOutcome leftSat leftUnsat)
      (AyAICOutcome rightSat rightUnsat) :=
  fun satForward satBackward unsatForward unsatBackward =>
    ay_aic_conj_intro
      (AyAICOutcome leftSat leftUnsat ->
        AyAICOutcome rightSat rightUnsat)
      (AyAICOutcome rightSat rightUnsat ->
        AyAICOutcome leftSat leftUnsat)
      (ay_aic_outcome_map leftSat rightSat leftUnsat rightUnsat
        satForward unsatForward)
      (ay_aic_outcome_map rightSat leftSat rightUnsat leftUnsat
        satBackward unsatBackward)

theorem ay_aic_compressed_expand (payload : Prop) :
    AyAICCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_aic_compressed_pack (payload : Prop) :
    payload -> AyAICCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_aic_compressed_roundtrip (payload : Prop) :
    AyAICEquisat (AyAICCompressed payload) payload :=
  ay_aic_conj_intro (AyAICCompressed payload -> payload)
    (payload -> AyAICCompressed payload)
    (ay_aic_compressed_expand payload)
    (ay_aic_compressed_pack payload)

theorem ay_aic_indexed_intro (index payload : Prop) :
    index -> payload -> AyAICIndexed index payload :=
  fun indexProof payloadProof =>
    ay_aic_conj_intro index payload indexProof payloadProof

theorem ay_aic_indexed_index (index payload : Prop) :
    AyAICIndexed index payload -> index :=
  fun indexed => ay_aic_conj_left index payload indexed

theorem ay_aic_indexed_payload (index payload : Prop) :
    AyAICIndexed index payload -> payload :=
  fun indexed => ay_aic_conj_right index payload indexed

theorem ay_aic_lookup_from_indexed (index payload : Prop) :
    AyAICIndexed index payload -> AyAICLookup index payload :=
  fun indexed _indexProof => ay_aic_indexed_payload index payload indexed

theorem ay_aic_indexed_lookup_sound (index payload : Prop) :
    AyAICLookup index payload -> index -> payload :=
  fun lookup indexProof => lookup indexProof

theorem ay_aic_indexed_compressed_lookup
    (index payload : Prop) :
    AyAICIndexed index (AyAICCompressed payload) ->
    index ->
    payload :=
  fun indexed indexProof =>
    ay_aic_compressed_expand payload
      (ay_aic_lookup_from_indexed index (AyAICCompressed payload) indexed
        indexProof)

theorem ay_aic_project_indexed_compressed
    (index payload visibleSat replayUnsat : Prop) :
    AyAICProjection payload visibleSat replayUnsat ->
    AyAICIndexed index (AyAICCompressed payload) ->
    index ->
    AyAICOutcome visibleSat replayUnsat :=
  fun project indexed indexProof =>
    project
      (ay_aic_indexed_compressed_lookup index payload indexed indexProof)

theorem ay_aic_reconstruct_indexed_compressed
    (index payload visibleSat replayUnsat : Prop) :
    index ->
    AyAICReconstruction visibleSat replayUnsat payload ->
    AyAICOutcome visibleSat replayUnsat ->
    AyAICIndexed index (AyAICCompressed payload) :=
  fun indexProof reconstruct outcome =>
    ay_aic_indexed_intro index (AyAICCompressed payload)
      indexProof
      (ay_aic_compressed_pack payload (reconstruct outcome))

theorem ay_aic_projection_reconstruction_roundtrip
    (payload visibleSat replayUnsat : Prop) :
    AyAICProjection payload visibleSat replayUnsat ->
    AyAICReconstruction visibleSat replayUnsat payload ->
    AyAICEquisat payload (AyAICOutcome visibleSat replayUnsat) :=
  fun project reconstruct =>
    ay_aic_conj_intro
      (payload -> AyAICOutcome visibleSat replayUnsat)
      (AyAICOutcome visibleSat replayUnsat -> payload)
      project reconstruct

theorem ay_aic_indexed_projection_reconstruction_roundtrip
    (index payload visibleSat replayUnsat : Prop) :
    index ->
    AyAICProjection payload visibleSat replayUnsat ->
    AyAICReconstruction visibleSat replayUnsat payload ->
    AyAICEquisat
      (AyAICIndexed index (AyAICCompressed payload))
      (AyAICOutcome visibleSat replayUnsat) :=
  fun indexProof project reconstruct =>
    ay_aic_conj_intro
      (AyAICIndexed index (AyAICCompressed payload) ->
        AyAICOutcome visibleSat replayUnsat)
      (AyAICOutcome visibleSat replayUnsat ->
        AyAICIndexed index (AyAICCompressed payload))
      (fun indexed =>
        ay_aic_project_indexed_compressed index payload visibleSat
          replayUnsat project indexed
          (ay_aic_indexed_index index (AyAICCompressed payload) indexed))
      (ay_aic_reconstruct_indexed_compressed index payload visibleSat
        replayUnsat indexProof reconstruct)

theorem ay_aic_visible_sat_forward
    (original solver internalAssignment visibleAssignment : Prop) :
    AyAICEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAICCDCLSat solver internalAssignment ->
    AyAICVisibleSAT original visibleAssignment :=
  fun preprocess decode sat =>
    ay_aic_model_intro original visibleAssignment
      (ay_aic_equisat_backward original solver preprocess
        (ay_aic_model_formula solver internalAssignment sat))
      (decode (ay_aic_model_assignment solver internalAssignment sat))

theorem ay_aic_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyAICReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyAICCDCLUnsat stream ->
    AyAICUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_aic_unsat_pullback
    (original solver : Prop) :
    AyAICEquisat original solver ->
    AyAICUnsat solver ->
    AyAICUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_aic_equisat_forward original solver preprocess originalProof)

theorem ay_aic_unsat_forward
    (original solver stream finalClause : Prop) :
    AyAICEquisat original solver ->
    AyAICReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyAICCDCLUnsat stream ->
    AyAICUnsat original :=
  fun preprocess replay closeFinal branch =>
    ay_aic_unsat_pullback original solver preprocess
      (ay_aic_replay_unsat_solver solver stream finalClause replay closeFinal
        branch)

theorem ay_aic_cdcl_to_visible_outcome
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyAICEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAICReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyAICOutcome
      (AyAICCDCLSat solver internalAssignment)
      (AyAICCDCLUnsat stream) ->
    AyAICOutcome
      (AyAICVisibleSAT original visibleAssignment)
      (AyAICUnsat original) :=
  fun preprocess decode replay closeFinal =>
    ay_aic_outcome_map
      (AyAICCDCLSat solver internalAssignment)
      (AyAICVisibleSAT original visibleAssignment)
      (AyAICCDCLUnsat stream)
      (AyAICUnsat original)
      (ay_aic_visible_sat_forward original solver internalAssignment
        visibleAssignment preprocess decode)
      (ay_aic_unsat_forward original solver stream finalClause preprocess
        replay closeFinal)

theorem ay_aic_indexed_compressed_top_sound
    (index original solver internalAssignment visibleAssignment stream
      finalClause : Prop) :
    AyAICEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyAICReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyAICIndexed index
      (AyAICCompressed
        (AyAICOutcome
          (AyAICCDCLSat solver internalAssignment)
          (AyAICCDCLUnsat stream))) ->
    index ->
    AyAICOutcome
      (AyAICVisibleSAT original visibleAssignment)
      (AyAICUnsat original) :=
  fun preprocess decode replay closeFinal indexed indexProof =>
    ay_aic_cdcl_to_visible_outcome original solver internalAssignment
      visibleAssignment stream finalClause preprocess decode replay closeFinal
      (ay_aic_indexed_compressed_lookup index
        (AyAICOutcome
          (AyAICCDCLSat solver internalAssignment)
          (AyAICCDCLUnsat stream))
        indexed indexProof)

theorem ay_aic_indexed_top_reconstruct
    (index original solver internalAssignment visibleAssignment stream
      finalClause : Prop) :
    index ->
    AyAICEquisat original solver ->
    (visibleAssignment -> internalAssignment) ->
    (AyAICUnsat solver -> AyAICCDCLUnsat stream) ->
    AyAICOutcome
      (AyAICVisibleSAT original visibleAssignment)
      (AyAICUnsat original) ->
    AyAICIndexed index
      (AyAICCompressed
        (AyAICOutcome
          (AyAICCDCLSat solver internalAssignment)
          (AyAICCDCLUnsat stream))) :=
  fun indexProof preprocess encodeSat encodeUnsat visibleOutcome =>
    ay_aic_reconstruct_indexed_compressed index
      (AyAICOutcome
        (AyAICCDCLSat solver internalAssignment)
        (AyAICCDCLUnsat stream))
      (AyAICVisibleSAT original visibleAssignment)
      (AyAICUnsat original)
      indexProof
      (ay_aic_outcome_map
        (AyAICVisibleSAT original visibleAssignment)
        (AyAICCDCLSat solver internalAssignment)
        (AyAICUnsat original)
        (AyAICCDCLUnsat stream)
        (fun visible =>
          ay_aic_model_intro solver internalAssignment
            (ay_aic_equisat_forward original solver preprocess
              (ay_aic_model_formula original visibleAssignment visible))
            (encodeSat
              (ay_aic_model_assignment original visibleAssignment visible)))
        (fun unsatOriginal =>
          encodeUnsat
            (fun solverProof =>
              unsatOriginal
                (ay_aic_equisat_backward original solver preprocess
                  solverProof))))
      visibleOutcome

theorem ay_aic_indexed_compressed_top_roundtrip
    (index original solver internalAssignment visibleAssignment stream
      finalClause : Prop) :
    index ->
    AyAICEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    (visibleAssignment -> internalAssignment) ->
    AyAICReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    (AyAICUnsat solver -> AyAICCDCLUnsat stream) ->
    AyAICEquisat
      (AyAICIndexed index
        (AyAICCompressed
          (AyAICOutcome
            (AyAICCDCLSat solver internalAssignment)
            (AyAICCDCLUnsat stream))))
      (AyAICOutcome
        (AyAICVisibleSAT original visibleAssignment)
        (AyAICUnsat original)) :=
  fun indexProof preprocess decode encode replay closeFinal encodeUnsat =>
    ay_aic_conj_intro
      (AyAICIndexed index
        (AyAICCompressed
          (AyAICOutcome
            (AyAICCDCLSat solver internalAssignment)
            (AyAICCDCLUnsat stream))) ->
        AyAICOutcome
          (AyAICVisibleSAT original visibleAssignment)
          (AyAICUnsat original))
      (AyAICOutcome
        (AyAICVisibleSAT original visibleAssignment)
        (AyAICUnsat original) ->
        AyAICIndexed index
          (AyAICCompressed
            (AyAICOutcome
              (AyAICCDCLSat solver internalAssignment)
              (AyAICCDCLUnsat stream))))
      (fun indexed =>
        ay_aic_indexed_compressed_top_sound index original solver
          internalAssignment visibleAssignment stream finalClause preprocess
          decode replay closeFinal indexed
          (ay_aic_indexed_index index
            (AyAICCompressed
              (AyAICOutcome
                (AyAICCDCLSat solver internalAssignment)
                (AyAICCDCLUnsat stream)))
            indexed))
      (ay_aic_indexed_top_reconstruct index original solver
        internalAssignment visibleAssignment stream finalClause indexProof
        preprocess encode encodeUnsat)
