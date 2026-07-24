-- SAT-COMP chronological/nonchronological backtracking plus restart core.
--
-- The statements are intentionally abstract: clauses, trails, and formula
-- states are propositions, and the certificate obligations are Church-encoded
-- maps between them.  This is the shape needed to hook solver backtracking and
-- restart certificates into later concrete SAT semantics.

def AyCBRConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCBRDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCBREquisat (before after : Prop) : Prop :=
  AyCBRConj (before -> after) (after -> before)

def AyCBRTransform (before after : Prop) : Prop :=
  AyCBREquisat before after

def AyCBRState (formula learned trail : Prop) : Prop :=
  AyCBRConj formula (AyCBRConj learned trail)

def AyCBRModel (formula trail : Prop) : Prop :=
  AyCBRConj formula trail

def AyCBRConflict (formula learned trail : Prop) : Prop :=
  formula -> learned -> trail -> False

def AyCBROutcome (model conflict : Prop) : Prop :=
  AyCBRDisj model conflict

def AyCBRTrailProjection (source target : Prop) : Prop :=
  source -> target

def AyCBRLearnedPreservation (before after : Prop) : Prop :=
  before -> after

theorem ay_cbr_conj_intro (left right : Prop) :
    left -> right -> AyCBRConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cbr_conj_left (left right : Prop) :
    AyCBRConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cbr_conj_right (left right : Prop) :
    AyCBRConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cbr_disj_left (left right : Prop) :
    left -> AyCBRDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cbr_disj_right (left right : Prop) :
    right -> AyCBRDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cbr_equisat_forward (before after : Prop) :
    AyCBREquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_cbr_equisat_backward (before after : Prop) :
    AyCBREquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_cbr_equisat_refl (formula : Prop) :
    AyCBREquisat formula formula :=
  ay_cbr_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_cbr_equisat_symm (before after : Prop) :
    AyCBREquisat before after -> AyCBREquisat after before :=
  fun witness result build =>
    witness result (fun forward backward => build backward forward)

theorem ay_cbr_transform_compose
    (first second third : Prop) :
    AyCBRTransform first second ->
    AyCBRTransform second third ->
    AyCBRTransform first third :=
  fun leftStep rightStep result build =>
    leftStep result
      (fun leftForward leftBackward =>
        rightStep result
          (fun rightForward rightBackward =>
            build
              (fun hfirst => rightForward (leftForward hfirst))
              (fun hthird => leftBackward (rightBackward hthird))))

theorem ay_cbr_state_intro (formula learned trail : Prop) :
    formula -> learned -> trail -> AyCBRState formula learned trail :=
  fun formulaProof learnedProof trailProof =>
    ay_cbr_conj_intro formula (AyCBRConj learned trail)
      formulaProof
      (ay_cbr_conj_intro learned trail learnedProof trailProof)

theorem ay_cbr_state_formula (formula learned trail : Prop) :
    AyCBRState formula learned trail -> formula :=
  fun state => state formula (fun formulaProof _tail => formulaProof)

theorem ay_cbr_state_learned (formula learned trail : Prop) :
    AyCBRState formula learned trail -> learned :=
  fun state =>
    state learned
      (fun _formulaProof tail =>
        tail learned (fun learnedProof _trailProof => learnedProof))

theorem ay_cbr_state_trail (formula learned trail : Prop) :
    AyCBRState formula learned trail -> trail :=
  fun state =>
    state trail
      (fun _formulaProof tail =>
        tail trail (fun _learnedProof trailProof => trailProof))

theorem ay_cbr_model_intro (formula trail : Prop) :
    formula -> trail -> AyCBRModel formula trail :=
  fun formulaProof trailProof =>
    ay_cbr_conj_intro formula trail formulaProof trailProof

theorem ay_cbr_model_formula (formula trail : Prop) :
    AyCBRModel formula trail -> formula :=
  fun model => ay_cbr_conj_left formula trail model

theorem ay_cbr_model_trail (formula trail : Prop) :
    AyCBRModel formula trail -> trail :=
  fun model => ay_cbr_conj_right formula trail model

theorem ay_cbr_trail_projection_refl (trail : Prop) :
    AyCBRTrailProjection trail trail :=
  fun proof => proof

theorem ay_cbr_trail_projection_compose
    (source middle target : Prop) :
    AyCBRTrailProjection source middle ->
    AyCBRTrailProjection middle target ->
    AyCBRTrailProjection source target :=
  fun first second sourceProof => second (first sourceProof)

theorem ay_cbr_project_trail_in_state
    (formula learned sourceTrail targetTrail : Prop) :
    AyCBRTrailProjection sourceTrail targetTrail ->
    AyCBRState formula learned sourceTrail ->
    AyCBRState formula learned targetTrail :=
  fun project state =>
    ay_cbr_state_intro formula learned targetTrail
      (ay_cbr_state_formula formula learned sourceTrail state)
      (ay_cbr_state_learned formula learned sourceTrail state)
      (project (ay_cbr_state_trail formula learned sourceTrail state))

theorem ay_cbr_trail_projection_equisat
    (formula learned sourceTrail targetTrail : Prop) :
    AyCBRTrailProjection sourceTrail targetTrail ->
    AyCBRTrailProjection targetTrail sourceTrail ->
    AyCBREquisat
      (AyCBRState formula learned sourceTrail)
      (AyCBRState formula learned targetTrail) :=
  fun forward backward =>
    ay_cbr_conj_intro
      (AyCBRState formula learned sourceTrail ->
        AyCBRState formula learned targetTrail)
      (AyCBRState formula learned targetTrail ->
        AyCBRState formula learned sourceTrail)
      (ay_cbr_project_trail_in_state formula learned sourceTrail targetTrail
        forward)
      (ay_cbr_project_trail_in_state formula learned targetTrail sourceTrail
        backward)

theorem ay_cbr_learned_preserved_by_projection
    (formula learned sourceTrail targetTrail : Prop) :
    AyCBRTrailProjection sourceTrail targetTrail ->
    AyCBRState formula learned sourceTrail ->
    learned :=
  fun _project state =>
    ay_cbr_state_learned formula learned sourceTrail state

theorem ay_cbr_learned_transport_in_state
    (formula beforeLearned afterLearned trail : Prop) :
    AyCBRLearnedPreservation beforeLearned afterLearned ->
    AyCBRState formula beforeLearned trail ->
    AyCBRState formula afterLearned trail :=
  fun preserve state =>
    ay_cbr_state_intro formula afterLearned trail
      (ay_cbr_state_formula formula beforeLearned trail state)
      (preserve (ay_cbr_state_learned formula beforeLearned trail state))
      (ay_cbr_state_trail formula beforeLearned trail state)

theorem ay_cbr_learned_equisat_lifts_to_state
    (formula beforeLearned afterLearned trail : Prop) :
    AyCBREquisat beforeLearned afterLearned ->
    AyCBREquisat
      (AyCBRState formula beforeLearned trail)
      (AyCBRState formula afterLearned trail) :=
  fun learnedMap =>
    ay_cbr_conj_intro
      (AyCBRState formula beforeLearned trail ->
        AyCBRState formula afterLearned trail)
      (AyCBRState formula afterLearned trail ->
        AyCBRState formula beforeLearned trail)
      (ay_cbr_learned_transport_in_state formula beforeLearned afterLearned
        trail (ay_cbr_equisat_forward beforeLearned afterLearned learnedMap))
      (ay_cbr_learned_transport_in_state formula afterLearned beforeLearned
        trail (ay_cbr_equisat_backward beforeLearned afterLearned learnedMap))

theorem ay_cbr_backjump_conflict_soundness
    (formula learned currentTrail jumpTrail : Prop) :
    AyCBRTrailProjection currentTrail jumpTrail ->
    AyCBRConflict formula learned jumpTrail ->
    AyCBRConflict formula learned currentTrail :=
  fun project conflict formulaProof learnedProof currentTrailProof =>
    conflict formulaProof learnedProof (project currentTrailProof)

theorem ay_cbr_chrono_backtrack_conflict_soundness
    (formula learned currentTrail previousTrail : Prop) :
    AyCBRTrailProjection currentTrail previousTrail ->
    AyCBRConflict formula learned previousTrail ->
    AyCBRConflict formula learned currentTrail :=
  ay_cbr_backjump_conflict_soundness formula learned currentTrail previousTrail

theorem ay_cbr_conflict_transport_formula
    (beforeFormula afterFormula learned trail : Prop) :
    (beforeFormula -> afterFormula) ->
    AyCBRConflict afterFormula learned trail ->
    AyCBRConflict beforeFormula learned trail :=
  fun formulaForward conflict beforeFormulaProof learnedProof trailProof =>
    conflict (formulaForward beforeFormulaProof) learnedProof trailProof

theorem ay_cbr_conflict_transport_learned
    (formula beforeLearned afterLearned trail : Prop) :
    (beforeLearned -> afterLearned) ->
    AyCBRConflict formula afterLearned trail ->
    AyCBRConflict formula beforeLearned trail :=
  fun learnedForward conflict formulaProof beforeLearnedProof trailProof =>
    conflict formulaProof (learnedForward beforeLearnedProof) trailProof

theorem ay_cbr_conflict_transport_trail
    (formula learned beforeTrail afterTrail : Prop) :
    AyCBRTrailProjection beforeTrail afterTrail ->
    AyCBRConflict formula learned afterTrail ->
    AyCBRConflict formula learned beforeTrail :=
  fun trailForward conflict formulaProof learnedProof beforeTrailProof =>
    conflict formulaProof learnedProof (trailForward beforeTrailProof)

theorem ay_cbr_restart_reset_preserves_formula_equisat
    (formula learned beforeTrail afterTrail : Prop) :
    AyCBRTrailProjection beforeTrail afterTrail ->
    AyCBRTrailProjection afterTrail beforeTrail ->
    AyCBREquisat
      (AyCBRState formula learned beforeTrail)
      (AyCBRState formula learned afterTrail) :=
  ay_cbr_trail_projection_equisat formula learned beforeTrail afterTrail

theorem ay_cbr_restart_reset_preserves_formula_projection
    (formula learned beforeTrail afterTrail : Prop) :
    AyCBRTrailProjection beforeTrail afterTrail ->
    AyCBRState formula learned beforeTrail ->
    formula :=
  fun _project state =>
    ay_cbr_state_formula formula learned beforeTrail state

theorem ay_cbr_formula_equisat_lifts_to_state
    (beforeFormula afterFormula learned trail : Prop) :
    AyCBREquisat beforeFormula afterFormula ->
    AyCBREquisat
      (AyCBRState beforeFormula learned trail)
      (AyCBRState afterFormula learned trail) :=
  fun formulaMap =>
    ay_cbr_conj_intro
      (AyCBRState beforeFormula learned trail ->
        AyCBRState afterFormula learned trail)
      (AyCBRState afterFormula learned trail ->
        AyCBRState beforeFormula learned trail)
      (fun state =>
        ay_cbr_state_intro afterFormula learned trail
          (ay_cbr_equisat_forward beforeFormula afterFormula formulaMap
            (ay_cbr_state_formula beforeFormula learned trail state))
          (ay_cbr_state_learned beforeFormula learned trail state)
          (ay_cbr_state_trail beforeFormula learned trail state))
      (fun state =>
        ay_cbr_state_intro beforeFormula learned trail
          (ay_cbr_equisat_backward beforeFormula afterFormula formulaMap
            (ay_cbr_state_formula afterFormula learned trail state))
          (ay_cbr_state_learned afterFormula learned trail state)
          (ay_cbr_state_trail afterFormula learned trail state))

theorem ay_cbr_model_transport
    (beforeFormula afterFormula beforeTrail afterTrail : Prop) :
    (beforeFormula -> afterFormula) ->
    AyCBRTrailProjection beforeTrail afterTrail ->
    AyCBRModel beforeFormula beforeTrail ->
    AyCBRModel afterFormula afterTrail :=
  fun formulaForward trailForward model =>
    ay_cbr_model_intro afterFormula afterTrail
      (formulaForward (ay_cbr_model_formula beforeFormula beforeTrail model))
      (trailForward (ay_cbr_model_trail beforeFormula beforeTrail model))

theorem ay_cbr_model_equisat_transport
    (beforeFormula afterFormula beforeTrail afterTrail : Prop) :
    AyCBREquisat beforeFormula afterFormula ->
    AyCBRTrailProjection beforeTrail afterTrail ->
    AyCBRTrailProjection afterTrail beforeTrail ->
    AyCBREquisat
      (AyCBRModel beforeFormula beforeTrail)
      (AyCBRModel afterFormula afterTrail) :=
  fun formulaMap trailForward trailBackward =>
    ay_cbr_conj_intro
      (AyCBRModel beforeFormula beforeTrail ->
        AyCBRModel afterFormula afterTrail)
      (AyCBRModel afterFormula afterTrail ->
        AyCBRModel beforeFormula beforeTrail)
      (ay_cbr_model_transport beforeFormula afterFormula beforeTrail
        afterTrail
        (ay_cbr_equisat_forward beforeFormula afterFormula formulaMap)
        trailForward)
      (ay_cbr_model_transport afterFormula beforeFormula afterTrail
        beforeTrail
        (ay_cbr_equisat_backward beforeFormula afterFormula formulaMap)
        trailBackward)

theorem ay_cbr_final_conflict_transport
    (beforeFormula afterFormula beforeLearned afterLearned beforeTrail afterTrail :
      Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeLearned -> afterLearned) ->
    AyCBRTrailProjection beforeTrail afterTrail ->
    AyCBRConflict afterFormula afterLearned afterTrail ->
    AyCBRConflict beforeFormula beforeLearned beforeTrail :=
  fun formulaForward learnedForward trailForward conflict formulaProof
      learnedProof trailProof =>
    conflict (formulaForward formulaProof) (learnedForward learnedProof)
      (trailForward trailProof)

theorem ay_cbr_final_outcome_transport
    (beforeModel afterModel beforeConflict afterConflict : Prop) :
    (beforeModel -> afterModel) ->
    (beforeConflict -> afterConflict) ->
    AyCBROutcome beforeModel beforeConflict ->
    AyCBROutcome afterModel afterConflict :=
  fun modelForward conflictForward outcome result onModel onConflict =>
    outcome result
      (fun modelProof => onModel (modelForward modelProof))
      (fun conflictProof => onConflict (conflictForward conflictProof))

theorem ay_cbr_backtrack_restart_pipeline
    (beforeFormula afterFormula learned currentTrail jumpTrail restartTrail :
      Prop) :
    AyCBREquisat beforeFormula afterFormula ->
    AyCBRTrailProjection currentTrail jumpTrail ->
    AyCBRTrailProjection jumpTrail restartTrail ->
    AyCBRTrailProjection restartTrail currentTrail ->
    AyCBREquisat
      (AyCBRState beforeFormula learned currentTrail)
      (AyCBRState afterFormula learned restartTrail) :=
  fun formulaMap projectJump restartForward restartBackward =>
    ay_cbr_transform_compose
      (AyCBRState beforeFormula learned currentTrail)
      (AyCBRState afterFormula learned currentTrail)
      (AyCBRState afterFormula learned restartTrail)
      (ay_cbr_formula_equisat_lifts_to_state beforeFormula afterFormula
        learned currentTrail formulaMap)
      (ay_cbr_trail_projection_equisat afterFormula learned currentTrail
        restartTrail
        (ay_cbr_trail_projection_compose currentTrail jumpTrail restartTrail
          projectJump restartForward)
        restartBackward)

theorem ay_cbr_pipeline_conflict_transport
    (beforeFormula afterFormula learned currentTrail jumpTrail restartTrail :
      Prop) :
    (beforeFormula -> afterFormula) ->
    AyCBRTrailProjection currentTrail jumpTrail ->
    AyCBRTrailProjection jumpTrail restartTrail ->
    AyCBRConflict afterFormula learned restartTrail ->
    AyCBRConflict beforeFormula learned currentTrail :=
  fun formulaForward projectJump restartForward conflict =>
    ay_cbr_conflict_transport_formula beforeFormula afterFormula learned
      currentTrail formulaForward
      (ay_cbr_conflict_transport_trail afterFormula learned currentTrail
        restartTrail
        (ay_cbr_trail_projection_compose currentTrail jumpTrail restartTrail
          projectJump restartForward)
        conflict)
