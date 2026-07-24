-- Minimal SAT-COMP certificate roundtrip theorem.
--
-- This file keeps only the top-level certificate interface: a visible SAT
-- branch, an UNSAT replay branch, and transport between CDCL outcomes and the
-- final competition-facing outcome.

def AyCTRConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCTRDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCTREquisat (before after : Prop) : Prop :=
  AyCTRConj (before -> after) (after -> before)

def AyCTRModel (formula assignment : Prop) : Prop :=
  AyCTRConj formula assignment

def AyCTRUnsat (formula : Prop) : Prop :=
  formula -> False

def AyCTROutcome (sat unsat : Prop) : Prop :=
  AyCTRDisj sat unsat

def AyCTRReplayCert (formula stream finalClause : Prop) : Prop :=
  stream -> formula -> finalClause

def AyCTRCDCLSat (solver internalAssignment : Prop) : Prop :=
  AyCTRModel solver internalAssignment

def AyCTRCDCLUnsat (stream : Prop) : Prop :=
  stream

def AyCTRVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyCTRModel original visibleAssignment

theorem ay_ctr_conj_intro (left right : Prop) :
    left -> right -> AyCTRConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ctr_conj_left (left right : Prop) :
    AyCTRConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ctr_conj_right (left right : Prop) :
    AyCTRConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ctr_disj_left (left right : Prop) :
    left -> AyCTRDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ctr_disj_right (left right : Prop) :
    right -> AyCTRDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ctr_equisat_forward (before after : Prop) :
    AyCTREquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_ctr_equisat_backward (before after : Prop) :
    AyCTREquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_ctr_equisat_refl (formula : Prop) :
    AyCTREquisat formula formula :=
  ay_ctr_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_ctr_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyCTRModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_ctr_conj_intro formula assignment formulaProof assignmentProof

theorem ay_ctr_model_formula (formula assignment : Prop) :
    AyCTRModel formula assignment -> formula :=
  fun model => ay_ctr_conj_left formula assignment model

theorem ay_ctr_model_assignment (formula assignment : Prop) :
    AyCTRModel formula assignment -> assignment :=
  fun model => ay_ctr_conj_right formula assignment model

theorem ay_ctr_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyCTROutcome beforeSat beforeUnsat ->
    AyCTROutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_ctr_outcome_roundtrip
    (leftSat rightSat leftUnsat rightUnsat : Prop) :
    (leftSat -> rightSat) ->
    (rightSat -> leftSat) ->
    (leftUnsat -> rightUnsat) ->
    (rightUnsat -> leftUnsat) ->
    AyCTREquisat
      (AyCTROutcome leftSat leftUnsat)
      (AyCTROutcome rightSat rightUnsat) :=
  fun satForward satBackward unsatForward unsatBackward =>
    ay_ctr_conj_intro
      (AyCTROutcome leftSat leftUnsat ->
        AyCTROutcome rightSat rightUnsat)
      (AyCTROutcome rightSat rightUnsat ->
        AyCTROutcome leftSat leftUnsat)
      (ay_ctr_outcome_map leftSat rightSat leftUnsat rightUnsat
        satForward unsatForward)
      (ay_ctr_outcome_map rightSat leftSat rightUnsat leftUnsat
        satBackward unsatBackward)

theorem ay_ctr_visible_sat_forward
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCTREquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCTRCDCLSat solver internalAssignment ->
    AyCTRVisibleSAT original visibleAssignment :=
  fun preprocess decode sat =>
    ay_ctr_model_intro original visibleAssignment
      (ay_ctr_equisat_backward original solver preprocess
        (ay_ctr_model_formula solver internalAssignment sat))
      (decode (ay_ctr_model_assignment solver internalAssignment sat))

theorem ay_ctr_visible_sat_backward
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCTREquisat original solver ->
    (visibleAssignment -> internalAssignment) ->
    AyCTRVisibleSAT original visibleAssignment ->
    AyCTRCDCLSat solver internalAssignment :=
  fun preprocess encode visible =>
    ay_ctr_model_intro solver internalAssignment
      (ay_ctr_equisat_forward original solver preprocess
        (ay_ctr_model_formula original visibleAssignment visible))
      (encode (ay_ctr_model_assignment original visibleAssignment visible))

theorem ay_ctr_replay_final_clause
    (solver stream finalClause : Prop) :
    AyCTRReplayCert solver stream finalClause ->
    AyCTRCDCLUnsat stream ->
    solver ->
    finalClause :=
  fun replay streamProof solverProof => replay streamProof solverProof

theorem ay_ctr_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyCTRReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTRCDCLUnsat stream ->
    AyCTRUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal
      (ay_ctr_replay_final_clause solver stream finalClause replay
        streamProof solverProof)

theorem ay_ctr_unsat_pullback
    (original solver : Prop) :
    AyCTREquisat original solver ->
    AyCTRUnsat solver ->
    AyCTRUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_ctr_equisat_forward original solver preprocess originalProof)

theorem ay_ctr_unsat_pushforward
    (original solver : Prop) :
    AyCTREquisat original solver ->
    AyCTRUnsat original ->
    AyCTRUnsat solver :=
  fun preprocess originalUnsat solverProof =>
    originalUnsat
      (ay_ctr_equisat_backward original solver preprocess solverProof)

theorem ay_ctr_unsat_replay_forward
    (original solver stream finalClause : Prop) :
    AyCTREquisat original solver ->
    AyCTRReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTRCDCLUnsat stream ->
    AyCTRUnsat original :=
  fun preprocess replay closeFinal branch =>
    ay_ctr_unsat_pullback original solver preprocess
      (ay_ctr_replay_unsat_solver solver stream finalClause replay closeFinal
        branch)

theorem ay_ctr_unsat_replay_backward
    (original solver stream : Prop) :
    AyCTREquisat original solver ->
    (AyCTRUnsat solver -> AyCTRCDCLUnsat stream) ->
    AyCTRUnsat original ->
    AyCTRCDCLUnsat stream :=
  fun preprocess encode originalUnsat =>
    encode (ay_ctr_unsat_pushforward original solver preprocess originalUnsat)

theorem ay_ctr_cdcl_to_visible_outcome
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyCTREquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCTRReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTROutcome
      (AyCTRCDCLSat solver internalAssignment)
      (AyCTRCDCLUnsat stream) ->
    AyCTROutcome
      (AyCTRVisibleSAT original visibleAssignment)
      (AyCTRUnsat original) :=
  fun preprocess decode replay closeFinal =>
    ay_ctr_outcome_map
      (AyCTRCDCLSat solver internalAssignment)
      (AyCTRVisibleSAT original visibleAssignment)
      (AyCTRCDCLUnsat stream)
      (AyCTRUnsat original)
      (ay_ctr_visible_sat_forward original solver internalAssignment
        visibleAssignment preprocess decode)
      (ay_ctr_unsat_replay_forward original solver stream finalClause
        preprocess replay closeFinal)

theorem ay_ctr_visible_to_cdcl_outcome
    (original solver internalAssignment visibleAssignment stream : Prop) :
    AyCTREquisat original solver ->
    (visibleAssignment -> internalAssignment) ->
    (AyCTRUnsat solver -> AyCTRCDCLUnsat stream) ->
    AyCTROutcome
      (AyCTRVisibleSAT original visibleAssignment)
      (AyCTRUnsat original) ->
    AyCTROutcome
      (AyCTRCDCLSat solver internalAssignment)
      (AyCTRCDCLUnsat stream) :=
  fun preprocess encodeSat encodeUnsat =>
    ay_ctr_outcome_map
      (AyCTRVisibleSAT original visibleAssignment)
      (AyCTRCDCLSat solver internalAssignment)
      (AyCTRUnsat original)
      (AyCTRCDCLUnsat stream)
      (ay_ctr_visible_sat_backward original solver internalAssignment
        visibleAssignment preprocess encodeSat)
      (ay_ctr_unsat_replay_backward original solver stream preprocess
        encodeUnsat)

theorem ay_ctr_competition_top_roundtrip
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyCTREquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    (visibleAssignment -> internalAssignment) ->
    AyCTRReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    (AyCTRUnsat solver -> AyCTRCDCLUnsat stream) ->
    AyCTREquisat
      (AyCTROutcome
        (AyCTRCDCLSat solver internalAssignment)
        (AyCTRCDCLUnsat stream))
      (AyCTROutcome
        (AyCTRVisibleSAT original visibleAssignment)
        (AyCTRUnsat original)) :=
  fun preprocess decode encode replay closeFinal encodeUnsat =>
    ay_ctr_outcome_roundtrip
      (AyCTRCDCLSat solver internalAssignment)
      (AyCTRVisibleSAT original visibleAssignment)
      (AyCTRCDCLUnsat stream)
      (AyCTRUnsat original)
      (ay_ctr_visible_sat_forward original solver internalAssignment
        visibleAssignment preprocess decode)
      (ay_ctr_visible_sat_backward original solver internalAssignment
        visibleAssignment preprocess encode)
      (ay_ctr_unsat_replay_forward original solver stream finalClause
        preprocess replay closeFinal)
      (ay_ctr_unsat_replay_backward original solver stream preprocess
        encodeUnsat)
