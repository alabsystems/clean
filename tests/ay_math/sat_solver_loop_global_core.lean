-- SAT-COMP global CDCL solver-loop soundness skeleton.
--
-- The objects here are abstract propositions.  The maps are explicit
-- forward/backward witnesses in the same Church-encoded style used by the
-- other Ay SAT math packages, so later concrete SAT semantics can instantiate
-- propagation, decisions, conflict analysis, learned clauses, restarts, and
-- preprocessing without changing this proof shape.

def AySLGConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AySLGDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AySLGEquisat (before after : Prop) : Prop :=
  AySLGConj (before -> after) (after -> before)

def AySLGTransform (before after : Prop) : Prop :=
  AySLGEquisat before after

def AySLGState (formula learned trail decisions : Prop) : Prop :=
  AySLGConj formula (AySLGConj learned (AySLGConj trail decisions))

def AySLGModel (formula trail decisions : Prop) : Prop :=
  AySLGConj formula (AySLGConj trail decisions)

def AySLGConflict (formula learned trail : Prop) : Prop :=
  formula -> learned -> trail -> False

def AySLGUnsat (formula learned : Prop) : Prop :=
  formula -> learned -> False

def AySLGOutcome (model unsat : Prop) : Prop :=
  AySLGDisj model unsat

def AySLGMap (before after : Prop) : Prop :=
  before -> after

def AySLGPropagation (beforeTrail afterTrail : Prop) : Prop :=
  beforeTrail -> afterTrail

def AySLGDecision (beforeTrail beforeDecisions afterTrail afterDecisions : Prop) :
    Prop :=
  beforeTrail -> beforeDecisions -> AySLGConj afterTrail afterDecisions

def AySLGLearnedStep (beforeLearned afterLearned : Prop) : Prop :=
  beforeLearned -> afterLearned

def AySLGConflictAnalysis
    (formula learned trail learnedClause : Prop) : Prop :=
  AySLGConflict formula learned trail -> learnedClause

theorem ay_slg_conj_intro (left right : Prop) :
    left -> right -> AySLGConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_slg_conj_left (left right : Prop) :
    AySLGConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_slg_conj_right (left right : Prop) :
    AySLGConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_slg_disj_left (left right : Prop) :
    left -> AySLGDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_slg_disj_right (left right : Prop) :
    right -> AySLGDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_slg_equisat_forward (before after : Prop) :
    AySLGEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_slg_equisat_backward (before after : Prop) :
    AySLGEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_slg_equisat_refl (formula : Prop) :
    AySLGEquisat formula formula :=
  ay_slg_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_slg_equisat_symm (before after : Prop) :
    AySLGEquisat before after -> AySLGEquisat after before :=
  fun witness result build =>
    witness result (fun forward backward => build backward forward)

theorem ay_slg_transform_compose (first second third : Prop) :
    AySLGTransform first second ->
    AySLGTransform second third ->
    AySLGTransform first third :=
  fun leftStep rightStep result build =>
    leftStep result
      (fun leftForward leftBackward =>
        rightStep result
          (fun rightForward rightBackward =>
            build
              (fun hfirst => rightForward (leftForward hfirst))
              (fun hthird => leftBackward (rightBackward hthird))))

theorem ay_slg_state_intro
    (formula learned trail decisions : Prop) :
    formula -> learned -> trail -> decisions ->
    AySLGState formula learned trail decisions :=
  fun formulaProof learnedProof trailProof decisionsProof =>
    ay_slg_conj_intro formula
      (AySLGConj learned (AySLGConj trail decisions))
      formulaProof
      (ay_slg_conj_intro learned (AySLGConj trail decisions)
        learnedProof
        (ay_slg_conj_intro trail decisions trailProof decisionsProof))

theorem ay_slg_state_formula
    (formula learned trail decisions : Prop) :
    AySLGState formula learned trail decisions -> formula :=
  fun state => state formula (fun formulaProof _rest => formulaProof)

theorem ay_slg_state_learned
    (formula learned trail decisions : Prop) :
    AySLGState formula learned trail decisions -> learned :=
  fun state =>
    state learned
      (fun _formulaProof rest =>
        rest learned (fun learnedProof _tail => learnedProof))

theorem ay_slg_state_trail
    (formula learned trail decisions : Prop) :
    AySLGState formula learned trail decisions -> trail :=
  fun state =>
    state trail
      (fun _formulaProof rest =>
        rest trail
          (fun _learnedProof tail =>
            tail trail (fun trailProof _decisionsProof => trailProof)))

theorem ay_slg_state_decisions
    (formula learned trail decisions : Prop) :
    AySLGState formula learned trail decisions -> decisions :=
  fun state =>
    state decisions
      (fun _formulaProof rest =>
        rest decisions
          (fun _learnedProof tail =>
            tail decisions (fun _trailProof decisionsProof => decisionsProof)))

theorem ay_slg_model_intro (formula trail decisions : Prop) :
    formula -> trail -> decisions -> AySLGModel formula trail decisions :=
  fun formulaProof trailProof decisionsProof =>
    ay_slg_conj_intro formula (AySLGConj trail decisions)
      formulaProof
      (ay_slg_conj_intro trail decisions trailProof decisionsProof)

theorem ay_slg_model_formula (formula trail decisions : Prop) :
    AySLGModel formula trail decisions -> formula :=
  fun model => model formula (fun formulaProof _tail => formulaProof)

theorem ay_slg_model_trail (formula trail decisions : Prop) :
    AySLGModel formula trail decisions -> trail :=
  fun model =>
    model trail
      (fun _formulaProof tail =>
        tail trail (fun trailProof _decisionsProof => trailProof))

theorem ay_slg_model_decisions (formula trail decisions : Prop) :
    AySLGModel formula trail decisions -> decisions :=
  fun model =>
    model decisions
      (fun _formulaProof tail =>
        tail decisions (fun _trailProof decisionsProof => decisionsProof))

theorem ay_slg_map_refl (value : Prop) :
    AySLGMap value value :=
  fun proof => proof

theorem ay_slg_map_compose (first second third : Prop) :
    AySLGMap first second ->
    AySLGMap second third ->
    AySLGMap first third :=
  fun left right proof => right (left proof)

theorem ay_slg_formula_map_lifts_to_state
    (beforeFormula afterFormula learned trail decisions : Prop) :
    AySLGEquisat beforeFormula afterFormula ->
    AySLGEquisat
      (AySLGState beforeFormula learned trail decisions)
      (AySLGState afterFormula learned trail decisions) :=
  fun formulaMap =>
    ay_slg_conj_intro
      (AySLGState beforeFormula learned trail decisions ->
        AySLGState afterFormula learned trail decisions)
      (AySLGState afterFormula learned trail decisions ->
        AySLGState beforeFormula learned trail decisions)
      (fun state =>
        ay_slg_state_intro afterFormula learned trail decisions
          (ay_slg_equisat_forward beforeFormula afterFormula formulaMap
            (ay_slg_state_formula beforeFormula learned trail decisions state))
          (ay_slg_state_learned beforeFormula learned trail decisions state)
          (ay_slg_state_trail beforeFormula learned trail decisions state)
          (ay_slg_state_decisions beforeFormula learned trail decisions state))
      (fun state =>
        ay_slg_state_intro beforeFormula learned trail decisions
          (ay_slg_equisat_backward beforeFormula afterFormula formulaMap
            (ay_slg_state_formula afterFormula learned trail decisions state))
          (ay_slg_state_learned afterFormula learned trail decisions state)
          (ay_slg_state_trail afterFormula learned trail decisions state)
          (ay_slg_state_decisions afterFormula learned trail decisions state))

theorem ay_slg_propagation_lifts_to_state
    (formula learned beforeTrail afterTrail decisions : Prop) :
    AySLGPropagation beforeTrail afterTrail ->
    AySLGState formula learned beforeTrail decisions ->
    AySLGState formula learned afterTrail decisions :=
  fun propagate state =>
    ay_slg_state_intro formula learned afterTrail decisions
      (ay_slg_state_formula formula learned beforeTrail decisions state)
      (ay_slg_state_learned formula learned beforeTrail decisions state)
      (propagate
        (ay_slg_state_trail formula learned beforeTrail decisions state))
      (ay_slg_state_decisions formula learned beforeTrail decisions state)

theorem ay_slg_propagation_equisat_state
    (formula learned beforeTrail afterTrail decisions : Prop) :
    AySLGPropagation beforeTrail afterTrail ->
    AySLGPropagation afterTrail beforeTrail ->
    AySLGEquisat
      (AySLGState formula learned beforeTrail decisions)
      (AySLGState formula learned afterTrail decisions) :=
  fun forward backward =>
    ay_slg_conj_intro
      (AySLGState formula learned beforeTrail decisions ->
        AySLGState formula learned afterTrail decisions)
      (AySLGState formula learned afterTrail decisions ->
        AySLGState formula learned beforeTrail decisions)
      (ay_slg_propagation_lifts_to_state formula learned beforeTrail
        afterTrail decisions forward)
      (ay_slg_propagation_lifts_to_state formula learned afterTrail
        beforeTrail decisions backward)

theorem ay_slg_decision_lifts_to_state
    (formula learned beforeTrail beforeDecisions afterTrail afterDecisions :
      Prop) :
    AySLGDecision beforeTrail beforeDecisions afterTrail afterDecisions ->
    AySLGState formula learned beforeTrail beforeDecisions ->
    AySLGState formula learned afterTrail afterDecisions :=
  fun decide state =>
    decide
      (ay_slg_state_trail formula learned beforeTrail beforeDecisions state)
      (ay_slg_state_decisions formula learned beforeTrail beforeDecisions state)
      (AySLGState formula learned afterTrail afterDecisions)
      (fun afterTrailProof afterDecisionsProof =>
        ay_slg_state_intro formula learned afterTrail afterDecisions
          (ay_slg_state_formula formula learned beforeTrail beforeDecisions
            state)
          (ay_slg_state_learned formula learned beforeTrail beforeDecisions
            state)
          afterTrailProof
          afterDecisionsProof)

theorem ay_slg_decision_equisat_state
    (formula learned beforeTrail beforeDecisions afterTrail afterDecisions :
      Prop) :
    AySLGDecision beforeTrail beforeDecisions afterTrail afterDecisions ->
    AySLGDecision afterTrail afterDecisions beforeTrail beforeDecisions ->
    AySLGEquisat
      (AySLGState formula learned beforeTrail beforeDecisions)
      (AySLGState formula learned afterTrail afterDecisions) :=
  fun forward backward =>
    ay_slg_conj_intro
      (AySLGState formula learned beforeTrail beforeDecisions ->
        AySLGState formula learned afterTrail afterDecisions)
      (AySLGState formula learned afterTrail afterDecisions ->
        AySLGState formula learned beforeTrail beforeDecisions)
      (ay_slg_decision_lifts_to_state formula learned beforeTrail
        beforeDecisions afterTrail afterDecisions forward)
      (ay_slg_decision_lifts_to_state formula learned afterTrail
        afterDecisions beforeTrail beforeDecisions backward)

theorem ay_slg_learned_lifts_to_state
    (formula beforeLearned afterLearned trail decisions : Prop) :
    AySLGLearnedStep beforeLearned afterLearned ->
    AySLGState formula beforeLearned trail decisions ->
    AySLGState formula afterLearned trail decisions :=
  fun learn state =>
    ay_slg_state_intro formula afterLearned trail decisions
      (ay_slg_state_formula formula beforeLearned trail decisions state)
      (learn (ay_slg_state_learned formula beforeLearned trail decisions state))
      (ay_slg_state_trail formula beforeLearned trail decisions state)
      (ay_slg_state_decisions formula beforeLearned trail decisions state)

theorem ay_slg_learned_equisat_state
    (formula beforeLearned afterLearned trail decisions : Prop) :
    AySLGEquisat beforeLearned afterLearned ->
    AySLGEquisat
      (AySLGState formula beforeLearned trail decisions)
      (AySLGState formula afterLearned trail decisions) :=
  fun learnedMap =>
    ay_slg_conj_intro
      (AySLGState formula beforeLearned trail decisions ->
        AySLGState formula afterLearned trail decisions)
      (AySLGState formula afterLearned trail decisions ->
        AySLGState formula beforeLearned trail decisions)
      (ay_slg_learned_lifts_to_state formula beforeLearned afterLearned
        trail decisions
        (ay_slg_equisat_forward beforeLearned afterLearned learnedMap))
      (ay_slg_learned_lifts_to_state formula afterLearned beforeLearned
        trail decisions
        (ay_slg_equisat_backward beforeLearned afterLearned learnedMap))

theorem ay_slg_conflict_analysis_produces_learned
    (formula learned trail learnedClause : Prop) :
    AySLGConflictAnalysis formula learned trail learnedClause ->
    AySLGConflict formula learned trail ->
    learnedClause :=
  fun analyze conflict => analyze conflict

theorem ay_slg_conflict_transport_formula
    (beforeFormula afterFormula learned trail : Prop) :
    (beforeFormula -> afterFormula) ->
    AySLGConflict afterFormula learned trail ->
    AySLGConflict beforeFormula learned trail :=
  fun formulaForward conflict beforeFormulaProof learnedProof trailProof =>
    conflict (formulaForward beforeFormulaProof) learnedProof trailProof

theorem ay_slg_conflict_transport_learned
    (formula beforeLearned afterLearned trail : Prop) :
    (beforeLearned -> afterLearned) ->
    AySLGConflict formula afterLearned trail ->
    AySLGConflict formula beforeLearned trail :=
  fun learnedForward conflict formulaProof beforeLearnedProof trailProof =>
    conflict formulaProof (learnedForward beforeLearnedProof) trailProof

theorem ay_slg_conflict_transport_trail
    (formula learned beforeTrail afterTrail : Prop) :
    (beforeTrail -> afterTrail) ->
    AySLGConflict formula learned afterTrail ->
    AySLGConflict formula learned beforeTrail :=
  fun trailForward conflict formulaProof learnedProof beforeTrailProof =>
    conflict formulaProof learnedProof (trailForward beforeTrailProof)

theorem ay_slg_restart_lifts_to_state
    (formula learned beforeTrail afterTrail decisions : Prop) :
    (beforeTrail -> afterTrail) ->
    AySLGState formula learned beforeTrail decisions ->
    AySLGState formula learned afterTrail decisions :=
  ay_slg_propagation_lifts_to_state formula learned beforeTrail afterTrail
    decisions

theorem ay_slg_restart_equisat_state
    (formula learned beforeTrail afterTrail decisions : Prop) :
    (beforeTrail -> afterTrail) ->
    (afterTrail -> beforeTrail) ->
    AySLGEquisat
      (AySLGState formula learned beforeTrail decisions)
      (AySLGState formula learned afterTrail decisions) :=
  ay_slg_propagation_equisat_state formula learned beforeTrail afterTrail
    decisions

theorem ay_slg_model_transport
    (beforeFormula afterFormula beforeTrail afterTrail beforeDecisions
      afterDecisions : Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeTrail -> afterTrail) ->
    (beforeDecisions -> afterDecisions) ->
    AySLGModel beforeFormula beforeTrail beforeDecisions ->
    AySLGModel afterFormula afterTrail afterDecisions :=
  fun formulaForward trailForward decisionsForward model =>
    ay_slg_model_intro afterFormula afterTrail afterDecisions
      (formulaForward
        (ay_slg_model_formula beforeFormula beforeTrail beforeDecisions model))
      (trailForward
        (ay_slg_model_trail beforeFormula beforeTrail beforeDecisions model))
      (decisionsForward
        (ay_slg_model_decisions beforeFormula beforeTrail beforeDecisions
          model))

theorem ay_slg_unsat_transport
    (beforeFormula afterFormula beforeLearned afterLearned : Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeLearned -> afterLearned) ->
    AySLGUnsat afterFormula afterLearned ->
    AySLGUnsat beforeFormula beforeLearned :=
  fun formulaForward learnedForward unsat formulaProof learnedProof =>
    unsat (formulaForward formulaProof) (learnedForward learnedProof)

theorem ay_slg_outcome_transport
    (beforeModel afterModel beforeUnsat afterUnsat : Prop) :
    (beforeModel -> afterModel) ->
    (beforeUnsat -> afterUnsat) ->
    AySLGOutcome beforeModel beforeUnsat ->
    AySLGOutcome afterModel afterUnsat :=
  fun modelForward unsatForward outcome result onModel onUnsat =>
    outcome result
      (fun modelProof => onModel (modelForward modelProof))
      (fun unsatProof => onUnsat (unsatForward unsatProof))

theorem ay_slg_preprocess_decide_propagate_learn_restart
    (sourceFormula prepFormula beforeLearned afterLearned startTrail
      decidedTrail propagatedTrail restartTrail startDecisions afterDecisions :
      Prop) :
    AySLGEquisat sourceFormula prepFormula ->
    AySLGDecision startTrail startDecisions decidedTrail afterDecisions ->
    AySLGDecision decidedTrail afterDecisions startTrail startDecisions ->
    AySLGPropagation decidedTrail propagatedTrail ->
    AySLGPropagation propagatedTrail decidedTrail ->
    AySLGEquisat beforeLearned afterLearned ->
    (propagatedTrail -> restartTrail) ->
    (restartTrail -> propagatedTrail) ->
    AySLGEquisat
      (AySLGState sourceFormula beforeLearned startTrail startDecisions)
      (AySLGState prepFormula afterLearned restartTrail afterDecisions) :=
  fun formulaMap decideForward decideBackward propagateForward
      propagateBackward learnedMap restartForward restartBackward =>
    ay_slg_transform_compose
      (AySLGState sourceFormula beforeLearned startTrail startDecisions)
      (AySLGState prepFormula beforeLearned startTrail startDecisions)
      (AySLGState prepFormula afterLearned restartTrail afterDecisions)
      (ay_slg_formula_map_lifts_to_state sourceFormula prepFormula
        beforeLearned startTrail startDecisions formulaMap)
      (ay_slg_transform_compose
        (AySLGState prepFormula beforeLearned startTrail startDecisions)
        (AySLGState prepFormula beforeLearned decidedTrail afterDecisions)
        (AySLGState prepFormula afterLearned restartTrail afterDecisions)
        (ay_slg_decision_equisat_state prepFormula beforeLearned startTrail
          startDecisions decidedTrail afterDecisions decideForward
          decideBackward)
        (ay_slg_transform_compose
          (AySLGState prepFormula beforeLearned decidedTrail afterDecisions)
          (AySLGState prepFormula beforeLearned propagatedTrail
            afterDecisions)
          (AySLGState prepFormula afterLearned restartTrail afterDecisions)
          (ay_slg_propagation_equisat_state prepFormula beforeLearned
            decidedTrail propagatedTrail afterDecisions propagateForward
            propagateBackward)
          (ay_slg_transform_compose
            (AySLGState prepFormula beforeLearned propagatedTrail
              afterDecisions)
            (AySLGState prepFormula afterLearned propagatedTrail
              afterDecisions)
            (AySLGState prepFormula afterLearned restartTrail afterDecisions)
            (ay_slg_learned_equisat_state prepFormula beforeLearned
              afterLearned propagatedTrail afterDecisions learnedMap)
            (ay_slg_restart_equisat_state prepFormula afterLearned
              propagatedTrail restartTrail afterDecisions restartForward
              restartBackward))))

theorem ay_slg_global_loop_forward
    (sourceFormula prepFormula beforeLearned afterLearned startTrail
      decidedTrail propagatedTrail restartTrail startDecisions afterDecisions :
      Prop) :
    AySLGEquisat sourceFormula prepFormula ->
    AySLGDecision startTrail startDecisions decidedTrail afterDecisions ->
    AySLGDecision decidedTrail afterDecisions startTrail startDecisions ->
    AySLGPropagation decidedTrail propagatedTrail ->
    AySLGPropagation propagatedTrail decidedTrail ->
    AySLGEquisat beforeLearned afterLearned ->
    (propagatedTrail -> restartTrail) ->
    (restartTrail -> propagatedTrail) ->
    AySLGState sourceFormula beforeLearned startTrail startDecisions ->
    AySLGState prepFormula afterLearned restartTrail afterDecisions :=
  fun formulaMap decideForward decideBackward propagateForward
      propagateBackward learnedMap restartForward restartBackward state =>
    ay_slg_equisat_forward
      (AySLGState sourceFormula beforeLearned startTrail startDecisions)
      (AySLGState prepFormula afterLearned restartTrail afterDecisions)
      (ay_slg_preprocess_decide_propagate_learn_restart sourceFormula
        prepFormula beforeLearned afterLearned startTrail decidedTrail
        propagatedTrail restartTrail startDecisions afterDecisions formulaMap
        decideForward decideBackward propagateForward propagateBackward
        learnedMap restartForward restartBackward)
      state

theorem ay_slg_final_sat_model_transport
    (visible sourceFormula prepFormula sourceTrail finalTrail sourceDecisions
      finalDecisions : Prop) :
    AySLGEquisat sourceFormula prepFormula ->
    (sourceTrail -> finalTrail) ->
    (finalTrail -> sourceTrail) ->
    (sourceDecisions -> finalDecisions) ->
    (finalDecisions -> sourceDecisions) ->
    (visible -> AySLGModel prepFormula finalTrail finalDecisions) ->
    visible ->
    AySLGModel sourceFormula sourceTrail sourceDecisions :=
  fun formulaMap trailForward trailBackward decisionsForward decisionsBackward
      decode visibleProof =>
    ay_slg_model_transport prepFormula sourceFormula finalTrail sourceTrail
      finalDecisions sourceDecisions
      (ay_slg_equisat_backward sourceFormula prepFormula formulaMap)
      trailBackward decisionsBackward (decode visibleProof)

theorem ay_slg_final_unsat_transport
    (sourceFormula prepFormula sourceLearned finalLearned : Prop) :
    AySLGEquisat sourceFormula prepFormula ->
    AySLGEquisat sourceLearned finalLearned ->
    AySLGUnsat prepFormula finalLearned ->
    AySLGUnsat sourceFormula sourceLearned :=
  fun formulaMap learnedMap unsat =>
    ay_slg_unsat_transport sourceFormula prepFormula sourceLearned
      finalLearned
      (ay_slg_equisat_forward sourceFormula prepFormula formulaMap)
      (ay_slg_equisat_forward sourceLearned finalLearned learnedMap)
      unsat

theorem ay_slg_final_outcome_transport
    (visibleModel visibleUnsat sourceFormula prepFormula sourceLearned
      finalLearned sourceTrail finalTrail sourceDecisions finalDecisions :
      Prop) :
    AySLGEquisat sourceFormula prepFormula ->
    AySLGEquisat sourceLearned finalLearned ->
    (sourceTrail -> finalTrail) ->
    (finalTrail -> sourceTrail) ->
    (sourceDecisions -> finalDecisions) ->
    (finalDecisions -> sourceDecisions) ->
    (visibleModel -> AySLGModel prepFormula finalTrail finalDecisions) ->
    (visibleUnsat -> AySLGUnsat prepFormula finalLearned) ->
    AySLGOutcome visibleModel visibleUnsat ->
    AySLGOutcome
      (AySLGModel sourceFormula sourceTrail sourceDecisions)
      (AySLGUnsat sourceFormula sourceLearned) :=
  fun formulaMap learnedMap trailForward trailBackward decisionsForward
      decisionsBackward decodeModel decodeUnsat outcome =>
    ay_slg_outcome_transport visibleModel
      (AySLGModel sourceFormula sourceTrail sourceDecisions)
      visibleUnsat
      (AySLGUnsat sourceFormula sourceLearned)
      (ay_slg_final_sat_model_transport visibleModel sourceFormula
        prepFormula sourceTrail finalTrail sourceDecisions finalDecisions
        formulaMap trailForward trailBackward decisionsForward
        decisionsBackward decodeModel)
      (fun unsatProof =>
        ay_slg_final_unsat_transport sourceFormula prepFormula sourceLearned
          finalLearned formulaMap learnedMap (decodeUnsat unsatProof))
      outcome
