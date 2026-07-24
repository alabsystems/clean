-- Minimal SAT-COMP certificate top theorem.
--
-- This package distills the competition certificate interface to the smallest
-- abstract surface: preprocessing, a CDCL SAT/UNSAT outcome, proof replay to a
-- final unsat clause, and transport to visible variables of the original
-- instance.

def AyCTMConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCTMDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCTMEquisat (before after : Prop) : Prop :=
  AyCTMConj (before -> after) (after -> before)

def AyCTMModel (formula assignment : Prop) : Prop :=
  AyCTMConj formula assignment

def AyCTMUnsat (formula : Prop) : Prop :=
  formula -> False

def AyCTMOutcome (sat unsat : Prop) : Prop :=
  AyCTMDisj sat unsat

def AyCTMReplayCert (formula stream finalClause : Prop) : Prop :=
  stream -> formula -> finalClause

def AyCTMCDCLSat (solverFormula internalAssignment : Prop) : Prop :=
  AyCTMModel solverFormula internalAssignment

def AyCTMCDCLUnsat (stream : Prop) : Prop :=
  stream

def AyCTMVisibleSAT (originalFormula visibleAssignment : Prop) : Prop :=
  AyCTMModel originalFormula visibleAssignment

theorem ay_ctm_conj_intro (left right : Prop) :
    left -> right -> AyCTMConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ctm_conj_left (left right : Prop) :
    AyCTMConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ctm_conj_right (left right : Prop) :
    AyCTMConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ctm_disj_left (left right : Prop) :
    left -> AyCTMDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ctm_disj_right (left right : Prop) :
    right -> AyCTMDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ctm_equisat_forward (before after : Prop) :
    AyCTMEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_ctm_equisat_backward (before after : Prop) :
    AyCTMEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_ctm_equisat_refl (formula : Prop) :
    AyCTMEquisat formula formula :=
  ay_ctm_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_ctm_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyCTMModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_ctm_conj_intro formula assignment formulaProof assignmentProof

theorem ay_ctm_model_formula (formula assignment : Prop) :
    AyCTMModel formula assignment -> formula :=
  fun model => ay_ctm_conj_left formula assignment model

theorem ay_ctm_model_assignment (formula assignment : Prop) :
    AyCTMModel formula assignment -> assignment :=
  fun model => ay_ctm_conj_right formula assignment model

theorem ay_ctm_visible_sat_transport
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCTMEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCTMCDCLSat solver internalAssignment ->
    AyCTMVisibleSAT original visibleAssignment :=
  fun preprocess decode sat =>
    ay_ctm_model_intro original visibleAssignment
      (ay_ctm_equisat_backward original solver preprocess
        (ay_ctm_model_formula solver internalAssignment sat))
      (decode (ay_ctm_model_assignment solver internalAssignment sat))

theorem ay_ctm_replay_final_clause
    (solver stream finalClause : Prop) :
    AyCTMReplayCert solver stream finalClause ->
    AyCTMCDCLUnsat stream ->
    solver ->
    finalClause :=
  fun replay streamProof solverProof => replay streamProof solverProof

theorem ay_ctm_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyCTMReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTMCDCLUnsat stream ->
    AyCTMUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal
      (ay_ctm_replay_final_clause solver stream finalClause replay
        streamProof solverProof)

theorem ay_ctm_unsat_pullback_preprocess
    (original solver : Prop) :
    AyCTMEquisat original solver ->
    AyCTMUnsat solver ->
    AyCTMUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_ctm_equisat_forward original solver preprocess originalProof)

theorem ay_ctm_visible_unsat_transport
    (original solver stream finalClause : Prop) :
    AyCTMEquisat original solver ->
    AyCTMReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTMCDCLUnsat stream ->
    AyCTMUnsat original :=
  fun preprocess replay closeFinal unsatBranch =>
    ay_ctm_unsat_pullback_preprocess original solver preprocess
      (ay_ctm_replay_unsat_solver solver stream finalClause replay closeFinal
        unsatBranch)

theorem ay_ctm_outcome_transport
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyCTMOutcome beforeSat beforeUnsat ->
    AyCTMOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_ctm_sat_branch_sound
    (original solver internalAssignment visibleAssignment finalUnsat : Prop) :
    AyCTMEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCTMCDCLSat solver internalAssignment ->
    AyCTMOutcome (AyCTMVisibleSAT original visibleAssignment) finalUnsat :=
  fun preprocess decode sat =>
    ay_ctm_disj_left (AyCTMVisibleSAT original visibleAssignment) finalUnsat
      (ay_ctm_visible_sat_transport original solver internalAssignment
        visibleAssignment preprocess decode sat)

theorem ay_ctm_unsat_branch_sound
    (original solver stream finalClause visibleSat : Prop) :
    AyCTMEquisat original solver ->
    AyCTMReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTMCDCLUnsat stream ->
    AyCTMOutcome visibleSat (AyCTMUnsat original) :=
  fun preprocess replay closeFinal unsatBranch =>
    ay_ctm_disj_right visibleSat (AyCTMUnsat original)
      (ay_ctm_visible_unsat_transport original solver stream finalClause
        preprocess replay closeFinal unsatBranch)

theorem ay_ctm_competition_top_minimal
    (visibleSat visibleUnsat original solver internalAssignment
      visibleAssignment stream finalClause : Prop) :
    AyCTMEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCTMReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    (visibleSat -> AyCTMCDCLSat solver internalAssignment) ->
    (visibleUnsat -> AyCTMCDCLUnsat stream) ->
    AyCTMOutcome visibleSat visibleUnsat ->
    AyCTMOutcome
      (AyCTMVisibleSAT original visibleAssignment)
      (AyCTMUnsat original) :=
  fun preprocess decode replay closeFinal decodeSat decodeUnsat outcome =>
    ay_ctm_outcome_transport visibleSat
      (AyCTMVisibleSAT original visibleAssignment)
      visibleUnsat
      (AyCTMUnsat original)
      (fun satProof =>
        ay_ctm_visible_sat_transport original solver internalAssignment
          visibleAssignment preprocess decode (decodeSat satProof))
      (fun unsatProof =>
        ay_ctm_visible_unsat_transport original solver stream finalClause
          preprocess replay closeFinal (decodeUnsat unsatProof))
      outcome

theorem ay_ctm_competition_top_from_cdcl_outcome
    (original solver internalAssignment visibleAssignment stream finalClause :
      Prop) :
    AyCTMEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCTMReplayCert solver stream finalClause ->
    (finalClause -> False) ->
    AyCTMOutcome
      (AyCTMCDCLSat solver internalAssignment)
      (AyCTMCDCLUnsat stream) ->
    AyCTMOutcome
      (AyCTMVisibleSAT original visibleAssignment)
      (AyCTMUnsat original) :=
  fun preprocess decode replay closeFinal outcome =>
    ay_ctm_competition_top_minimal
      (AyCTMCDCLSat solver internalAssignment)
      (AyCTMCDCLUnsat stream)
      original solver internalAssignment visibleAssignment stream finalClause
      preprocess decode replay closeFinal (fun sat => sat) (fun unsat => unsat)
      outcome
