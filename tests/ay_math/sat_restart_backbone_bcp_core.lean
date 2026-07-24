-- SAT-COMP restart/backtracking, backbone propagation, and BCP core.
--
-- This package keeps the objects abstract and Church-encoded.  It captures the
-- certificate interfaces needed when a restart resets the trail, backbone units
-- are enqueued again, and BCP either extends the trail soundly or transports a
-- conflict certificate back to the visible solver state.

def AyRBBConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyRBBDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyRBBEquisat (before after : Prop) : Prop :=
  AyRBBConj (before -> after) (after -> before)

def AyRBBTransform (before after : Prop) : Prop :=
  AyRBBEquisat before after

def AyRBBState (formula learned backbone trail : Prop) : Prop :=
  AyRBBConj formula (AyRBBConj learned (AyRBBConj backbone trail))

def AyRBBModel (formula backbone trail : Prop) : Prop :=
  AyRBBConj formula (AyRBBConj backbone trail)

def AyRBBConflict (formula learned backbone trail : Prop) : Prop :=
  formula -> learned -> backbone -> trail -> False

def AyRBBOutcome (model conflict : Prop) : Prop :=
  AyRBBDisj model conflict

def AyRBBTrailProjection (source target : Prop) : Prop :=
  source -> target

def AyRBBPreservation (before after : Prop) : Prop :=
  before -> after

def AyRBBUnitEnqueue (backbone beforeTrail afterTrail : Prop) : Prop :=
  backbone -> beforeTrail -> afterTrail

theorem ay_rbb_conj_intro (left right : Prop) :
    left -> right -> AyRBBConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_rbb_conj_left (left right : Prop) :
    AyRBBConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_rbb_conj_right (left right : Prop) :
    AyRBBConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_rbb_disj_left (left right : Prop) :
    left -> AyRBBDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_rbb_disj_right (left right : Prop) :
    right -> AyRBBDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_rbb_equisat_forward (before after : Prop) :
    AyRBBEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_rbb_equisat_backward (before after : Prop) :
    AyRBBEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_rbb_equisat_refl (formula : Prop) :
    AyRBBEquisat formula formula :=
  ay_rbb_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_rbb_transform_compose (first second third : Prop) :
    AyRBBTransform first second ->
    AyRBBTransform second third ->
    AyRBBTransform first third :=
  fun leftStep rightStep result build =>
    leftStep result
      (fun leftForward leftBackward =>
        rightStep result
          (fun rightForward rightBackward =>
            build
              (fun hfirst => rightForward (leftForward hfirst))
              (fun hthird => leftBackward (rightBackward hthird))))

theorem ay_rbb_state_intro
    (formula learned backbone trail : Prop) :
    formula -> learned -> backbone -> trail ->
    AyRBBState formula learned backbone trail :=
  fun formulaProof learnedProof backboneProof trailProof =>
    ay_rbb_conj_intro formula
      (AyRBBConj learned (AyRBBConj backbone trail))
      formulaProof
      (ay_rbb_conj_intro learned (AyRBBConj backbone trail)
        learnedProof
        (ay_rbb_conj_intro backbone trail backboneProof trailProof))

theorem ay_rbb_state_formula
    (formula learned backbone trail : Prop) :
    AyRBBState formula learned backbone trail -> formula :=
  fun state => state formula (fun formulaProof _rest => formulaProof)

theorem ay_rbb_state_learned
    (formula learned backbone trail : Prop) :
    AyRBBState formula learned backbone trail -> learned :=
  fun state =>
    state learned
      (fun _formulaProof rest =>
        rest learned (fun learnedProof _tail => learnedProof))

theorem ay_rbb_state_backbone
    (formula learned backbone trail : Prop) :
    AyRBBState formula learned backbone trail -> backbone :=
  fun state =>
    state backbone
      (fun _formulaProof rest =>
        rest backbone
          (fun _learnedProof tail =>
            tail backbone (fun backboneProof _trailProof => backboneProof)))

theorem ay_rbb_state_trail
    (formula learned backbone trail : Prop) :
    AyRBBState formula learned backbone trail -> trail :=
  fun state =>
    state trail
      (fun _formulaProof rest =>
        rest trail
          (fun _learnedProof tail =>
            tail trail (fun _backboneProof trailProof => trailProof)))

theorem ay_rbb_model_intro (formula backbone trail : Prop) :
    formula -> backbone -> trail -> AyRBBModel formula backbone trail :=
  fun formulaProof backboneProof trailProof =>
    ay_rbb_conj_intro formula (AyRBBConj backbone trail)
      formulaProof
      (ay_rbb_conj_intro backbone trail backboneProof trailProof)

theorem ay_rbb_model_formula (formula backbone trail : Prop) :
    AyRBBModel formula backbone trail -> formula :=
  fun model => model formula (fun formulaProof _tail => formulaProof)

theorem ay_rbb_model_backbone (formula backbone trail : Prop) :
    AyRBBModel formula backbone trail -> backbone :=
  fun model =>
    model backbone
      (fun _formulaProof tail =>
        tail backbone (fun backboneProof _trailProof => backboneProof))

theorem ay_rbb_model_trail (formula backbone trail : Prop) :
    AyRBBModel formula backbone trail -> trail :=
  fun model =>
    model trail
      (fun _formulaProof tail =>
        tail trail (fun _backboneProof trailProof => trailProof))

theorem ay_rbb_trail_projection_refl (trail : Prop) :
    AyRBBTrailProjection trail trail :=
  fun proof => proof

theorem ay_rbb_trail_projection_compose
    (source middle target : Prop) :
    AyRBBTrailProjection source middle ->
    AyRBBTrailProjection middle target ->
    AyRBBTrailProjection source target :=
  fun first second sourceProof => second (first sourceProof)

theorem ay_rbb_project_state_trail
    (formula learned backbone sourceTrail targetTrail : Prop) :
    AyRBBTrailProjection sourceTrail targetTrail ->
    AyRBBState formula learned backbone sourceTrail ->
    AyRBBState formula learned backbone targetTrail :=
  fun project state =>
    ay_rbb_state_intro formula learned backbone targetTrail
      (ay_rbb_state_formula formula learned backbone sourceTrail state)
      (ay_rbb_state_learned formula learned backbone sourceTrail state)
      (ay_rbb_state_backbone formula learned backbone sourceTrail state)
      (project (ay_rbb_state_trail formula learned backbone sourceTrail state))

theorem ay_rbb_restart_reset_preserves_state
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBTrailProjection afterTrail beforeTrail ->
    AyRBBEquisat
      (AyRBBState formula learned backbone beforeTrail)
      (AyRBBState formula learned backbone afterTrail) :=
  fun resetForward resetBackward =>
    ay_rbb_conj_intro
      (AyRBBState formula learned backbone beforeTrail ->
        AyRBBState formula learned backbone afterTrail)
      (AyRBBState formula learned backbone afterTrail ->
        AyRBBState formula learned backbone beforeTrail)
      (ay_rbb_project_state_trail formula learned backbone beforeTrail
        afterTrail resetForward)
      (ay_rbb_project_state_trail formula learned backbone afterTrail
        beforeTrail resetBackward)

theorem ay_rbb_learned_preserved_across_reset
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBState formula learned backbone beforeTrail ->
    learned :=
  fun _reset state =>
    ay_rbb_state_learned formula learned backbone beforeTrail state

theorem ay_rbb_backbone_preserved_across_reset
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBState formula learned backbone beforeTrail ->
    backbone :=
  fun _reset state =>
    ay_rbb_state_backbone formula learned backbone beforeTrail state

theorem ay_rbb_unit_enqueue_state
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBUnitEnqueue backbone beforeTrail afterTrail ->
    AyRBBState formula learned backbone beforeTrail ->
    AyRBBState formula learned backbone afterTrail :=
  fun enqueue state =>
    ay_rbb_state_intro formula learned backbone afterTrail
      (ay_rbb_state_formula formula learned backbone beforeTrail state)
      (ay_rbb_state_learned formula learned backbone beforeTrail state)
      (ay_rbb_state_backbone formula learned backbone beforeTrail state)
      (enqueue
        (ay_rbb_state_backbone formula learned backbone beforeTrail state)
        (ay_rbb_state_trail formula learned backbone beforeTrail state))

theorem ay_rbb_unit_enqueue_soundness
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBUnitEnqueue backbone beforeTrail afterTrail ->
    AyRBBState formula learned backbone beforeTrail ->
    afterTrail :=
  fun enqueue state =>
    ay_rbb_state_trail formula learned backbone afterTrail
      (ay_rbb_unit_enqueue_state formula learned backbone beforeTrail
        afterTrail enqueue state)

theorem ay_rbb_learned_transport_in_state
    (formula beforeLearned afterLearned backbone trail : Prop) :
    AyRBBPreservation beforeLearned afterLearned ->
    AyRBBState formula beforeLearned backbone trail ->
    AyRBBState formula afterLearned backbone trail :=
  fun preserve state =>
    ay_rbb_state_intro formula afterLearned backbone trail
      (ay_rbb_state_formula formula beforeLearned backbone trail state)
      (preserve
        (ay_rbb_state_learned formula beforeLearned backbone trail state))
      (ay_rbb_state_backbone formula beforeLearned backbone trail state)
      (ay_rbb_state_trail formula beforeLearned backbone trail state)

theorem ay_rbb_backbone_transport_in_state
    (formula learned beforeBackbone afterBackbone trail : Prop) :
    AyRBBPreservation beforeBackbone afterBackbone ->
    AyRBBState formula learned beforeBackbone trail ->
    AyRBBState formula learned afterBackbone trail :=
  fun preserve state =>
    ay_rbb_state_intro formula learned afterBackbone trail
      (ay_rbb_state_formula formula learned beforeBackbone trail state)
      (ay_rbb_state_learned formula learned beforeBackbone trail state)
      (preserve
        (ay_rbb_state_backbone formula learned beforeBackbone trail state))
      (ay_rbb_state_trail formula learned beforeBackbone trail state)

theorem ay_rbb_conflict_transport_formula
    (beforeFormula afterFormula learned backbone trail : Prop) :
    (beforeFormula -> afterFormula) ->
    AyRBBConflict afterFormula learned backbone trail ->
    AyRBBConflict beforeFormula learned backbone trail :=
  fun formulaForward conflict beforeFormulaProof learnedProof backboneProof
      trailProof =>
    conflict (formulaForward beforeFormulaProof) learnedProof backboneProof
      trailProof

theorem ay_rbb_conflict_transport_learned
    (formula beforeLearned afterLearned backbone trail : Prop) :
    (beforeLearned -> afterLearned) ->
    AyRBBConflict formula afterLearned backbone trail ->
    AyRBBConflict formula beforeLearned backbone trail :=
  fun learnedForward conflict formulaProof beforeLearnedProof backboneProof
      trailProof =>
    conflict formulaProof (learnedForward beforeLearnedProof) backboneProof
      trailProof

theorem ay_rbb_conflict_transport_backbone
    (formula learned beforeBackbone afterBackbone trail : Prop) :
    (beforeBackbone -> afterBackbone) ->
    AyRBBConflict formula learned afterBackbone trail ->
    AyRBBConflict formula learned beforeBackbone trail :=
  fun backboneForward conflict formulaProof learnedProof beforeBackboneProof
      trailProof =>
    conflict formulaProof learnedProof (backboneForward beforeBackboneProof)
      trailProof

theorem ay_rbb_conflict_transport_trail
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBConflict formula learned backbone afterTrail ->
    AyRBBConflict formula learned backbone beforeTrail :=
  fun trailForward conflict formulaProof learnedProof backboneProof
      beforeTrailProof =>
    conflict formulaProof learnedProof backboneProof
      (trailForward beforeTrailProof)

theorem ay_rbb_bcp_conflict_after_enqueue
    (formula learned backbone beforeTrail afterTrail : Prop) :
    AyRBBUnitEnqueue backbone beforeTrail afterTrail ->
    AyRBBConflict formula learned backbone afterTrail ->
    AyRBBConflict formula learned backbone beforeTrail :=
  fun enqueue conflict formulaProof learnedProof backboneProof
      beforeTrailProof =>
    conflict formulaProof learnedProof backboneProof
      (enqueue backboneProof beforeTrailProof)

theorem ay_rbb_model_transport
    (beforeFormula afterFormula beforeBackbone afterBackbone beforeTrail
      afterTrail : Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeBackbone -> afterBackbone) ->
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBModel beforeFormula beforeBackbone beforeTrail ->
    AyRBBModel afterFormula afterBackbone afterTrail :=
  fun formulaForward backboneForward trailForward model =>
    ay_rbb_model_intro afterFormula afterBackbone afterTrail
      (formulaForward
        (ay_rbb_model_formula beforeFormula beforeBackbone beforeTrail model))
      (backboneForward
        (ay_rbb_model_backbone beforeFormula beforeBackbone beforeTrail model))
      (trailForward
        (ay_rbb_model_trail beforeFormula beforeBackbone beforeTrail model))

theorem ay_rbb_model_equisat_transport
    (beforeFormula afterFormula beforeBackbone afterBackbone beforeTrail
      afterTrail : Prop) :
    AyRBBEquisat beforeFormula afterFormula ->
    AyRBBEquisat beforeBackbone afterBackbone ->
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBTrailProjection afterTrail beforeTrail ->
    AyRBBEquisat
      (AyRBBModel beforeFormula beforeBackbone beforeTrail)
      (AyRBBModel afterFormula afterBackbone afterTrail) :=
  fun formulaMap backboneMap trailForward trailBackward =>
    ay_rbb_conj_intro
      (AyRBBModel beforeFormula beforeBackbone beforeTrail ->
        AyRBBModel afterFormula afterBackbone afterTrail)
      (AyRBBModel afterFormula afterBackbone afterTrail ->
        AyRBBModel beforeFormula beforeBackbone beforeTrail)
      (ay_rbb_model_transport beforeFormula afterFormula beforeBackbone
        afterBackbone beforeTrail afterTrail
        (ay_rbb_equisat_forward beforeFormula afterFormula formulaMap)
        (ay_rbb_equisat_forward beforeBackbone afterBackbone backboneMap)
        trailForward)
      (ay_rbb_model_transport afterFormula beforeFormula afterBackbone
        beforeBackbone afterTrail beforeTrail
        (ay_rbb_equisat_backward beforeFormula afterFormula formulaMap)
        (ay_rbb_equisat_backward beforeBackbone afterBackbone backboneMap)
        trailBackward)

theorem ay_rbb_outcome_transport
    (beforeModel afterModel beforeConflict afterConflict : Prop) :
    (beforeModel -> afterModel) ->
    (beforeConflict -> afterConflict) ->
    AyRBBOutcome beforeModel beforeConflict ->
    AyRBBOutcome afterModel afterConflict :=
  fun modelForward conflictForward outcome result onModel onConflict =>
    outcome result
      (fun modelProof => onModel (modelForward modelProof))
      (fun conflictProof => onConflict (conflictForward conflictProof))

theorem ay_rbb_restart_backbone_bcp_pipeline
    (formula learned backbone beforeTrail resetTrail enqueueTrail : Prop) :
    AyRBBTrailProjection beforeTrail resetTrail ->
    AyRBBTrailProjection resetTrail beforeTrail ->
    AyRBBUnitEnqueue backbone resetTrail enqueueTrail ->
    AyRBBState formula learned backbone beforeTrail ->
    AyRBBState formula learned backbone enqueueTrail :=
  fun resetForward _resetBackward enqueue state =>
    ay_rbb_unit_enqueue_state formula learned backbone resetTrail enqueueTrail
      enqueue
      (ay_rbb_project_state_trail formula learned backbone beforeTrail
        resetTrail resetForward state)

theorem ay_rbb_restart_backbone_bcp_conflict_transport
    (formula learned backbone beforeTrail resetTrail enqueueTrail : Prop) :
    AyRBBTrailProjection beforeTrail resetTrail ->
    AyRBBUnitEnqueue backbone resetTrail enqueueTrail ->
    AyRBBConflict formula learned backbone enqueueTrail ->
    AyRBBConflict formula learned backbone beforeTrail :=
  fun resetForward enqueue conflict =>
    ay_rbb_conflict_transport_trail formula learned backbone beforeTrail
      resetTrail resetForward
      (ay_rbb_bcp_conflict_after_enqueue formula learned backbone resetTrail
        enqueueTrail enqueue conflict)

theorem ay_rbb_final_visible_model_reconstruction
    (visible beforeFormula afterFormula beforeBackbone afterBackbone beforeTrail
      afterTrail : Prop) :
    AyRBBEquisat beforeFormula afterFormula ->
    AyRBBEquisat beforeBackbone afterBackbone ->
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBTrailProjection afterTrail beforeTrail ->
    (visible -> AyRBBModel afterFormula afterBackbone afterTrail) ->
    visible ->
    AyRBBModel beforeFormula beforeBackbone beforeTrail :=
  fun formulaMap backboneMap trailForward trailBackward decode visibleProof =>
    ay_rbb_equisat_backward
      (AyRBBModel beforeFormula beforeBackbone beforeTrail)
      (AyRBBModel afterFormula afterBackbone afterTrail)
      (ay_rbb_model_equisat_transport beforeFormula afterFormula
        beforeBackbone afterBackbone beforeTrail afterTrail formulaMap
        backboneMap trailForward trailBackward)
      (decode visibleProof)

theorem ay_rbb_final_visible_conflict_transport
    (beforeFormula afterFormula beforeLearned afterLearned beforeBackbone
      afterBackbone beforeTrail afterTrail : Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeLearned -> afterLearned) ->
    (beforeBackbone -> afterBackbone) ->
    AyRBBTrailProjection beforeTrail afterTrail ->
    AyRBBConflict afterFormula afterLearned afterBackbone afterTrail ->
    AyRBBConflict beforeFormula beforeLearned beforeBackbone beforeTrail :=
  fun formulaForward learnedForward backboneForward trailForward conflict
      formulaProof learnedProof backboneProof trailProof =>
    conflict (formulaForward formulaProof) (learnedForward learnedProof)
      (backboneForward backboneProof) (trailForward trailProof)
