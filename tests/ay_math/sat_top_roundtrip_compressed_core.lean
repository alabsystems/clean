-- SAT-COMP top roundtrip with compressed outcome certificates.
--
-- This self-contained package adds one abstraction over the top-level
-- roundtrip theorem: a compact certificate that expands to a CDCL SAT/UNSAT
-- outcome, then transports to the visible competition outcome.

def AyTRCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyTRCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyTRCEquisat (before after : Prop) : Prop :=
  AyTRCConj (before -> after) (after -> before)

def AyTRCModel (formula assignment : Prop) : Prop :=
  AyTRCConj formula assignment

def AyTRCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyTRCOutcome (sat unsat : Prop) : Prop :=
  AyTRCDisj sat unsat

def AyTRCReplayCert (formula stream finalClause : Prop) : Prop :=
  stream -> formula -> finalClause

def AyTRCCompressed (payload : Prop) : Prop :=
  payload

def AyTRCCDCLSat (solver internalAssignment : Prop) : Prop :=
  AyTRCModel solver internalAssignment

def AyTRCCDCLUnsat (stream : Prop) : Prop :=
  stream

def AyTRCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyTRCModel original visibleAssignment

theorem ay_trc_conj_intro (left right : Prop) :
    left -> right -> AyTRCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_trc_conj_left (left right : Prop) :
    AyTRCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_trc_conj_right (left right : Prop) :
    AyTRCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_trc_disj_left (left right : Prop) :
    left -> AyTRCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_trc_disj_right (left right : Prop) :
    right -> AyTRCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_trc_equisat_forward (before after : Prop) :
    AyTRCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_trc_equisat_backward (before after : Prop) :
    AyTRCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_trc_equisat_refl (formula : Prop) :
    AyTRCEquisat formula formula :=
  ay_trc_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_trc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyTRCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_trc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_trc_model_formula (formula assignment : Prop) :
    AyTRCModel formula assignment -> formula :=
  fun model => ay_trc_conj_left formula assignment model

theorem ay_trc_model_assignment (formula assignment : Prop) :
    AyTRCModel formula assignment -> assignment :=
  fun model => ay_trc_conj_right formula assignment model

theorem ay_trc_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyTRCOutcome beforeSat beforeUnsat ->
    AyTRCOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_trc_outcome_roundtrip
    (leftSat rightSat leftUnsat rightUnsat : Prop) :
    (leftSat -> rightSat) ->
    (rightSat -> leftSat) ->
    (leftUnsat -> rightUnsat) ->
    (rightUnsat -> leftUnsat) ->
    AyTRCEquisat
      (AyTRCOutcome leftSat leftUnsat)
      (AyTRCOutcome rightSat rightUnsat) :=
  fun satForward satBackward unsatForward unsatBackward =>
    ay_trc_conj_intro
      (AyTRCOutcome leftSat leftUnsat ->
        AyTRCOutcome rightSat rightUnsat)
      (AyTRCOutcome rightSat rightUnsat ->
        AyTRCOutcome leftSat leftUnsat)
      (ay_trc_outcome_map leftSat rightSat leftUnsat rightUnsat
        satForward unsatForward)
      (ay_trc_outcome_map rightSat leftSat rightUnsat leftUnsat
        satBackward unsatBackward)

theorem ay_trc_compressed_expand (payload : Prop) :
    AyTRCCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_trc_compressed_pack (payload : Prop) :
    payload -> AyTRCCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_trc_compressed_roundtrip (payload : Prop) :
    AyTRCEquisat (AyTRCCompressed payload) payload :=
  ay_trc_conj_intro (AyTRCCompressed payload -> payload)
    (payload -> AyTRCCompressed payload)
    (ay_trc_compressed_expand payload)
    (ay_trc_compressed_pack payload)

theorem ay_trc_compressed_outcome_expand
    (sat unsat : Prop) :
    AyTRCCompressed (AyTRCOutcome sat unsat) ->
    AyTRCOutcome sat unsat :=
  ay_trc_compressed_expand (AyTRCOutcome sat unsat)

theorem ay_trc_compressed_outcome_pack
    (sat unsat : Prop) :
    AyTRCOutcome sat unsat ->
    AyTRCCompressed (AyTRCOutcome sat unsat) :=
  ay_trc_compressed_pack (AyTRCOutcome sat unsat)

theorem ay_trc_visible_sat_forward
    (original solver internalAssignment visibleAssignment : Prop) :
    AyTRCEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyTRCCDCLSat solver internalAssignment ->
    AyTRCVisibleSAT original visibleAssignment :=
  fun preprocess decode sat =>
    ay_trc_model_intro original visibleAssignment
      (ay_trc_equisat_backward original solver preprocess
        (ay_trc_model_formula solver internalAssignment sat))
      (decode (ay_trc_model_assignment solver internalAssignment sat))

theorem ay_trc_visible_sat_backward
    (original solver internalAssignment visibleAssignment : Prop) :
    AyTRCEquisat original solver ->
    (visibleAssignment -> internalAssignment) ->
    AyTRCVisibleSAT original visibleAssignment ->
    AyTRCCDCLSat solver internalAssignment :=
  fun preprocess encode visible =>
    ay_trc_model_intro solver internalAssignment
      (ay_trc_equisat_forward original solver preprocess
        (ay_trc_model_formula original visibleAssignment visible))
      (encode (ay_trc_model_assignment original visibleAssignment visible))

theorem ay_trc_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyTRCReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyTRCCDCLUnsat stream ->
    AyTRCUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_trc_unsat_pullback
    (original solver : Prop) :
    AyTRCEquisat original solver ->
    AyTRCUnsat solver ->
    AyTRCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_trc_equisat_forward original solver preprocess originalProof)

theorem ay_trc_unsat_pushforward
    (original solver : Prop) :
    AyTRCEquisat original solver ->
    AyTRCUnsat original ->
    AyTRCUnsat solver :=
  fun preprocess originalUnsat solverProof =>
    originalUnsat
      (ay_trc_equisat_backward original solver preprocess solverProof)

theorem ay_trc_unsat_forward
    (original solver stream finalClause : Prop) :
    AyTRCEquisat original solver ->
    AyTRCReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyTRCCDCLUnsat stream ->
    AyTRCUnsat original :=
  fun preprocess replay closeFinal branch =>
    ay_trc_unsat_pullback original solver preprocess
      (ay_trc_replay_unsat_solver solver stream finalClause replay closeFinal
        branch)

theorem ay_trc_unsat_backward
    (original solver stream : Prop) :
    AyTRCEquisat original solver ->
    (AyTRCUnsat solver -> AyTRCCDCLUnsat stream) ->
    AyTRCUnsat original ->
    AyTRCCDCLUnsat stream :=
  fun preprocess encode originalUnsat =>
    encode (ay_trc_unsat_pushforward original solver preprocess originalUnsat)

theorem ay_trc_cdcl_to_visible_outcome
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyTRCEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyTRCReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyTRCOutcome
      (AyTRCCDCLSat solver internalAssignment)
      (AyTRCCDCLUnsat stream) ->
    AyTRCOutcome
      (AyTRCVisibleSAT original visibleAssignment)
      (AyTRCUnsat original) :=
  fun preprocess decode replay closeFinal =>
    ay_trc_outcome_map
      (AyTRCCDCLSat solver internalAssignment)
      (AyTRCVisibleSAT original visibleAssignment)
      (AyTRCCDCLUnsat stream)
      (AyTRCUnsat original)
      (ay_trc_visible_sat_forward original solver internalAssignment
        visibleAssignment preprocess decode)
      (ay_trc_unsat_forward original solver stream finalClause preprocess
        replay closeFinal)

theorem ay_trc_visible_to_cdcl_outcome
    (original solver internalAssignment visibleAssignment stream : Prop) :
    AyTRCEquisat original solver ->
    (visibleAssignment -> internalAssignment) ->
    (AyTRCUnsat solver -> AyTRCCDCLUnsat stream) ->
    AyTRCOutcome
      (AyTRCVisibleSAT original visibleAssignment)
      (AyTRCUnsat original) ->
    AyTRCOutcome
      (AyTRCCDCLSat solver internalAssignment)
      (AyTRCCDCLUnsat stream) :=
  fun preprocess encodeSat encodeUnsat =>
    ay_trc_outcome_map
      (AyTRCVisibleSAT original visibleAssignment)
      (AyTRCCDCLSat solver internalAssignment)
      (AyTRCUnsat original)
      (AyTRCCDCLUnsat stream)
      (ay_trc_visible_sat_backward original solver internalAssignment
        visibleAssignment preprocess encodeSat)
      (ay_trc_unsat_backward original solver stream preprocess encodeUnsat)

theorem ay_trc_compressed_cdcl_to_visible
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyTRCEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyTRCReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyTRCCompressed
      (AyTRCOutcome
        (AyTRCCDCLSat solver internalAssignment)
        (AyTRCCDCLUnsat stream)) ->
    AyTRCOutcome
      (AyTRCVisibleSAT original visibleAssignment)
      (AyTRCUnsat original) :=
  fun preprocess decode replay closeFinal compressed =>
    ay_trc_cdcl_to_visible_outcome original solver internalAssignment
      visibleAssignment stream finalClause preprocess decode replay closeFinal
      (ay_trc_compressed_outcome_expand
        (AyTRCCDCLSat solver internalAssignment)
        (AyTRCCDCLUnsat stream)
        compressed)

theorem ay_trc_visible_to_compressed_cdcl
    (original solver internalAssignment visibleAssignment stream : Prop) :
    AyTRCEquisat original solver ->
    (visibleAssignment -> internalAssignment) ->
    (AyTRCUnsat solver -> AyTRCCDCLUnsat stream) ->
    AyTRCOutcome
      (AyTRCVisibleSAT original visibleAssignment)
      (AyTRCUnsat original) ->
    AyTRCCompressed
      (AyTRCOutcome
        (AyTRCCDCLSat solver internalAssignment)
        (AyTRCCDCLUnsat stream)) :=
  fun preprocess encodeSat encodeUnsat visibleOutcome =>
    ay_trc_compressed_outcome_pack
      (AyTRCCDCLSat solver internalAssignment)
      (AyTRCCDCLUnsat stream)
      (ay_trc_visible_to_cdcl_outcome original solver internalAssignment
        visibleAssignment stream preprocess encodeSat encodeUnsat
        visibleOutcome)

theorem ay_trc_top_roundtrip_compressed
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyTRCEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    (visibleAssignment -> internalAssignment) ->
    AyTRCReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    (AyTRCUnsat solver -> AyTRCCDCLUnsat stream) ->
    AyTRCEquisat
      (AyTRCCompressed
        (AyTRCOutcome
          (AyTRCCDCLSat solver internalAssignment)
          (AyTRCCDCLUnsat stream)))
      (AyTRCOutcome
        (AyTRCVisibleSAT original visibleAssignment)
        (AyTRCUnsat original)) :=
  fun preprocess decode encode replay closeFinal encodeUnsat =>
    ay_trc_conj_intro
      (AyTRCCompressed
        (AyTRCOutcome
          (AyTRCCDCLSat solver internalAssignment)
          (AyTRCCDCLUnsat stream)) ->
        AyTRCOutcome
          (AyTRCVisibleSAT original visibleAssignment)
          (AyTRCUnsat original))
      (AyTRCOutcome
        (AyTRCVisibleSAT original visibleAssignment)
        (AyTRCUnsat original) ->
        AyTRCCompressed
          (AyTRCOutcome
            (AyTRCCDCLSat solver internalAssignment)
            (AyTRCCDCLUnsat stream)))
      (ay_trc_compressed_cdcl_to_visible original solver internalAssignment
        visibleAssignment stream finalClause preprocess decode replay
        closeFinal)
      (ay_trc_visible_to_compressed_cdcl original solver internalAssignment
        visibleAssignment stream preprocess encode encodeUnsat)
