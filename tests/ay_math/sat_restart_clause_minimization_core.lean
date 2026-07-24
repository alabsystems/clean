-- SAT-COMP restart/clause-minimization core.
--
-- This file is self-contained on purpose.  It packages the abstract proof
-- obligations needed when a solver minimizes a learned clause, survives a
-- restart/trail reset, and then composes the step with preprocessing or
-- inprocessing maps.

def AyRestartMinConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyRestartMinDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyRestartMinEquisat (before after : Prop) : Prop :=
  AyRestartMinConj (before -> after) (after -> before)

def AyRestartMinTransform (before after : Prop) : Prop :=
  AyRestartMinEquisat before after

def AyRestartMinState (formula learned assumptions : Prop) : Prop :=
  AyRestartMinConj formula (AyRestartMinConj learned assumptions)

def AyRestartMinLearnedClause (context clause : Prop) : Prop :=
  AyRestartMinConj context clause

def AyRestartMinClauseOriginal (lit shorter rest : Prop) : Prop :=
  AyRestartMinConj (AyRestartMinDisj lit shorter) rest

def AyRestartMinClauseMinimized (shorter rest : Prop) : Prop :=
  AyRestartMinConj shorter rest

def AyRestartMinImpWitness (strong weak : Prop) : Prop :=
  strong -> weak

def AyRestartMinConflictWitness (formula learned : Prop) : Prop :=
  formula -> learned -> False

theorem ay_restart_min_conj_intro (left right : Prop) :
    left -> right -> AyRestartMinConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_restart_min_conj_left (left right : Prop) :
    AyRestartMinConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_restart_min_conj_right (left right : Prop) :
    AyRestartMinConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_restart_min_disj_left (left right : Prop) :
    left -> AyRestartMinDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_restart_min_disj_right (left right : Prop) :
    right -> AyRestartMinDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_restart_min_equisat_forward (before after : Prop) :
    AyRestartMinEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_restart_min_equisat_backward (before after : Prop) :
    AyRestartMinEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_restart_min_equisat_refl (formula : Prop) :
    AyRestartMinEquisat formula formula :=
  ay_restart_min_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_restart_min_equisat_symm (before after : Prop) :
    AyRestartMinEquisat before after -> AyRestartMinEquisat after before :=
  fun witness result build =>
    witness result (fun forward backward => build backward forward)

theorem ay_restart_min_transform_compose
    (first second third : Prop) :
    AyRestartMinTransform first second ->
    AyRestartMinTransform second third ->
    AyRestartMinTransform first third :=
  fun leftStep rightStep result build =>
    leftStep result
      (fun leftForward leftBackward =>
        rightStep result
          (fun rightForward rightBackward =>
            build
              (fun hfirst => rightForward (leftForward hfirst))
              (fun hthird => leftBackward (rightBackward hthird))))

theorem ay_restart_min_clause_forward
    (lit shorter rest : Prop) :
    AyRestartMinImpWitness lit shorter ->
    AyRestartMinClauseOriginal lit shorter rest ->
    AyRestartMinClauseMinimized shorter rest :=
  fun witness original result build =>
    original result
      (fun disj restProof =>
        disj result
          (fun litProof => build (witness litProof) restProof)
          (fun shorterProof => build shorterProof restProof))

theorem ay_restart_min_clause_backward
    (lit shorter rest : Prop) :
    AyRestartMinClauseMinimized shorter rest ->
    AyRestartMinClauseOriginal lit shorter rest :=
  fun minimized result build =>
    minimized result
      (fun shorterProof restProof =>
        build
          (ay_restart_min_disj_right lit shorter shorterProof)
          restProof)

theorem ay_restart_min_clause_equisat
    (lit shorter rest : Prop) :
    AyRestartMinImpWitness lit shorter ->
    AyRestartMinEquisat
      (AyRestartMinClauseOriginal lit shorter rest)
      (AyRestartMinClauseMinimized shorter rest) :=
  fun witness =>
    ay_restart_min_conj_intro
      (AyRestartMinClauseOriginal lit shorter rest ->
        AyRestartMinClauseMinimized shorter rest)
      (AyRestartMinClauseMinimized shorter rest ->
        AyRestartMinClauseOriginal lit shorter rest)
      (ay_restart_min_clause_forward lit shorter rest witness)
      (ay_restart_min_clause_backward lit shorter rest)

theorem ay_restart_min_learned_forward
    (context original minimized : Prop) :
    (original -> minimized) ->
    AyRestartMinLearnedClause context original ->
    AyRestartMinLearnedClause context minimized :=
  fun minimize learned result build =>
    learned result
      (fun contextProof originalProof =>
        build contextProof (minimize originalProof))

theorem ay_restart_min_learned_backward
    (context original minimized : Prop) :
    (minimized -> original) ->
    AyRestartMinLearnedClause context minimized ->
    AyRestartMinLearnedClause context original :=
  fun expand learned result build =>
    learned result
      (fun contextProof minimizedProof =>
        build contextProof (expand minimizedProof))

theorem ay_restart_min_learned_equisat
    (context original minimized : Prop) :
    AyRestartMinEquisat original minimized ->
    AyRestartMinEquisat
      (AyRestartMinLearnedClause context original)
      (AyRestartMinLearnedClause context minimized) :=
  fun clauseMap =>
    ay_restart_min_conj_intro
      (AyRestartMinLearnedClause context original ->
        AyRestartMinLearnedClause context minimized)
      (AyRestartMinLearnedClause context minimized ->
        AyRestartMinLearnedClause context original)
      (ay_restart_min_learned_forward context original minimized
        (ay_restart_min_equisat_forward original minimized clauseMap))
      (ay_restart_min_learned_backward context original minimized
        (ay_restart_min_equisat_backward original minimized clauseMap))

theorem ay_restart_min_state_formula (formula learned assumptions : Prop) :
    AyRestartMinState formula learned assumptions -> formula :=
  fun state => state formula (fun formulaProof _tail => formulaProof)

theorem ay_restart_min_state_learned (formula learned assumptions : Prop) :
    AyRestartMinState formula learned assumptions -> learned :=
  fun state =>
    state learned
      (fun _formulaProof tail =>
        tail learned (fun learnedProof _assumptionsProof => learnedProof))

theorem ay_restart_min_state_assumptions (formula learned assumptions : Prop) :
    AyRestartMinState formula learned assumptions -> assumptions :=
  fun state =>
    state assumptions
      (fun _formulaProof tail =>
        tail assumptions
          (fun _learnedProof assumptionsProof => assumptionsProof))

theorem ay_restart_min_state_intro
    (formula learned assumptions : Prop) :
    formula -> learned -> assumptions ->
    AyRestartMinState formula learned assumptions :=
  fun formulaProof learnedProof assumptionsProof =>
    ay_restart_min_conj_intro formula
      (AyRestartMinConj learned assumptions)
      formulaProof
      (ay_restart_min_conj_intro learned assumptions learnedProof
        assumptionsProof)

theorem ay_restart_min_state_minimize_forward
    (formula assumptions original minimized : Prop) :
    (original -> minimized) ->
    AyRestartMinState formula original assumptions ->
    AyRestartMinState formula minimized assumptions :=
  fun minimize state =>
    ay_restart_min_state_intro formula minimized assumptions
      (ay_restart_min_state_formula formula original assumptions state)
      (minimize
        (ay_restart_min_state_learned formula original assumptions state))
      (ay_restart_min_state_assumptions formula original assumptions state)

theorem ay_restart_min_state_minimize_backward
    (formula assumptions original minimized : Prop) :
    (minimized -> original) ->
    AyRestartMinState formula minimized assumptions ->
    AyRestartMinState formula original assumptions :=
  fun expand state =>
    ay_restart_min_state_intro formula original assumptions
      (ay_restart_min_state_formula formula minimized assumptions state)
      (expand
        (ay_restart_min_state_learned formula minimized assumptions state))
      (ay_restart_min_state_assumptions formula minimized assumptions state)

theorem ay_restart_min_state_minimize_equisat
    (formula assumptions original minimized : Prop) :
    AyRestartMinEquisat original minimized ->
    AyRestartMinEquisat
      (AyRestartMinState formula original assumptions)
      (AyRestartMinState formula minimized assumptions) :=
  fun clauseMap =>
    ay_restart_min_conj_intro
      (AyRestartMinState formula original assumptions ->
        AyRestartMinState formula minimized assumptions)
      (AyRestartMinState formula minimized assumptions ->
        AyRestartMinState formula original assumptions)
      (ay_restart_min_state_minimize_forward formula assumptions original
        minimized (ay_restart_min_equisat_forward original minimized clauseMap))
      (ay_restart_min_state_minimize_backward formula assumptions original
        minimized (ay_restart_min_equisat_backward original minimized clauseMap))

theorem ay_restart_min_conflict_transport_to_minimized
    (formula original minimized : Prop) :
    (minimized -> original) ->
    AyRestartMinConflictWitness formula original ->
    AyRestartMinConflictWitness formula minimized :=
  fun expand conflict formulaProof minimizedProof =>
    conflict formulaProof (expand minimizedProof)

theorem ay_restart_min_conflict_transport_from_minimized
    (formula original minimized : Prop) :
    (original -> minimized) ->
    AyRestartMinConflictWitness formula minimized ->
    AyRestartMinConflictWitness formula original :=
  fun minimize conflict formulaProof originalProof =>
    conflict formulaProof (minimize originalProof)

theorem ay_restart_min_conflict_preserved_by_equisat
    (formula original minimized : Prop) :
    AyRestartMinEquisat original minimized ->
    AyRestartMinEquisat
      (AyRestartMinConflictWitness formula original)
      (AyRestartMinConflictWitness formula minimized) :=
  fun clauseMap =>
    ay_restart_min_conj_intro
      (AyRestartMinConflictWitness formula original ->
        AyRestartMinConflictWitness formula minimized)
      (AyRestartMinConflictWitness formula minimized ->
        AyRestartMinConflictWitness formula original)
      (ay_restart_min_conflict_transport_to_minimized formula original
        minimized (ay_restart_min_equisat_backward original minimized clauseMap))
      (ay_restart_min_conflict_transport_from_minimized formula original
        minimized (ay_restart_min_equisat_forward original minimized clauseMap))

theorem ay_restart_min_reset_carries_clause
    (formula learned beforeTrail afterTrail : Prop) :
    (beforeTrail -> afterTrail) ->
    (afterTrail -> beforeTrail) ->
    AyRestartMinEquisat
      (AyRestartMinState formula learned beforeTrail)
      (AyRestartMinState formula learned afterTrail) :=
  fun resetForward resetBackward =>
    ay_restart_min_conj_intro
      (AyRestartMinState formula learned beforeTrail ->
        AyRestartMinState formula learned afterTrail)
      (AyRestartMinState formula learned afterTrail ->
        AyRestartMinState formula learned beforeTrail)
      (fun state =>
        ay_restart_min_state_intro formula learned afterTrail
          (ay_restart_min_state_formula formula learned beforeTrail state)
          (ay_restart_min_state_learned formula learned beforeTrail state)
          (resetForward
            (ay_restart_min_state_assumptions formula learned beforeTrail
              state)))
      (fun state =>
        ay_restart_min_state_intro formula learned beforeTrail
          (ay_restart_min_state_formula formula learned afterTrail state)
          (ay_restart_min_state_learned formula learned afterTrail state)
          (resetBackward
            (ay_restart_min_state_assumptions formula learned afterTrail
              state)))

theorem ay_restart_min_restart_reset_refl
    (formula learned trail : Prop) :
    AyRestartMinEquisat
      (AyRestartMinState formula learned trail)
      (AyRestartMinState formula learned trail) :=
  ay_restart_min_reset_carries_clause formula learned trail trail
    (fun h => h) (fun h => h)

theorem ay_restart_min_formula_map_lifts_to_state
    (beforeFormula afterFormula learned assumptions : Prop) :
    AyRestartMinEquisat beforeFormula afterFormula ->
    AyRestartMinEquisat
      (AyRestartMinState beforeFormula learned assumptions)
      (AyRestartMinState afterFormula learned assumptions) :=
  fun formulaMap =>
    ay_restart_min_conj_intro
      (AyRestartMinState beforeFormula learned assumptions ->
        AyRestartMinState afterFormula learned assumptions)
      (AyRestartMinState afterFormula learned assumptions ->
        AyRestartMinState beforeFormula learned assumptions)
      (fun state =>
        ay_restart_min_state_intro afterFormula learned assumptions
          (ay_restart_min_equisat_forward beforeFormula afterFormula
            formulaMap
            (ay_restart_min_state_formula beforeFormula learned assumptions
              state))
          (ay_restart_min_state_learned beforeFormula learned assumptions
            state)
          (ay_restart_min_state_assumptions beforeFormula learned assumptions
            state))
      (fun state =>
        ay_restart_min_state_intro beforeFormula learned assumptions
          (ay_restart_min_equisat_backward beforeFormula afterFormula
            formulaMap
            (ay_restart_min_state_formula afterFormula learned assumptions
              state))
          (ay_restart_min_state_learned afterFormula learned assumptions
            state)
          (ay_restart_min_state_assumptions afterFormula learned assumptions
            state))

theorem ay_restart_min_inprocess_minimize_pipeline
    (beforeFormula afterFormula assumptions original minimized : Prop) :
    AyRestartMinEquisat beforeFormula afterFormula ->
    AyRestartMinEquisat original minimized ->
    AyRestartMinEquisat
      (AyRestartMinState beforeFormula original assumptions)
      (AyRestartMinState afterFormula minimized assumptions) :=
  fun formulaMap clauseMap =>
    ay_restart_min_transform_compose
      (AyRestartMinState beforeFormula original assumptions)
      (AyRestartMinState afterFormula original assumptions)
      (AyRestartMinState afterFormula minimized assumptions)
      (ay_restart_min_formula_map_lifts_to_state beforeFormula afterFormula
        original assumptions formulaMap)
      (ay_restart_min_state_minimize_equisat afterFormula assumptions original
        minimized clauseMap)

theorem ay_restart_minimize_reset_inprocess_pipeline
    (beforeFormula afterFormula beforeTrail afterTrail original minimized : Prop) :
    AyRestartMinEquisat beforeFormula afterFormula ->
    AyRestartMinEquisat original minimized ->
    (beforeTrail -> afterTrail) ->
    (afterTrail -> beforeTrail) ->
    AyRestartMinEquisat
      (AyRestartMinState beforeFormula original beforeTrail)
      (AyRestartMinState afterFormula minimized afterTrail) :=
  fun formulaMap clauseMap resetForward resetBackward =>
    ay_restart_min_transform_compose
      (AyRestartMinState beforeFormula original beforeTrail)
      (AyRestartMinState afterFormula minimized beforeTrail)
      (AyRestartMinState afterFormula minimized afterTrail)
      (ay_restart_min_inprocess_minimize_pipeline beforeFormula afterFormula
        beforeTrail original minimized formulaMap clauseMap)
      (ay_restart_min_reset_carries_clause afterFormula minimized beforeTrail
        afterTrail resetForward resetBackward)

theorem ay_restart_min_clause_pipeline_from_implication
    (formula beforeTrail afterTrail lit shorter rest : Prop) :
    AyRestartMinImpWitness lit shorter ->
    (beforeTrail -> afterTrail) ->
    (afterTrail -> beforeTrail) ->
    AyRestartMinEquisat
      (AyRestartMinState formula
        (AyRestartMinClauseOriginal lit shorter rest)
        beforeTrail)
      (AyRestartMinState formula
        (AyRestartMinClauseMinimized shorter rest)
        afterTrail) :=
  fun implication resetForward resetBackward =>
    ay_restart_minimize_reset_inprocess_pipeline
      formula formula beforeTrail afterTrail
      (AyRestartMinClauseOriginal lit shorter rest)
      (AyRestartMinClauseMinimized shorter rest)
      (ay_restart_min_equisat_refl formula)
      (ay_restart_min_clause_equisat lit shorter rest implication)
      resetForward resetBackward

theorem ay_restart_min_final_visible_model_reconstruction
    (visible beforeFormula afterFormula beforeTrail afterTrail original minimized : Prop) :
    AyRestartMinEquisat beforeFormula afterFormula ->
    AyRestartMinEquisat original minimized ->
    (beforeTrail -> afterTrail) ->
    (afterTrail -> beforeTrail) ->
    (visible -> AyRestartMinState afterFormula minimized afterTrail) ->
    visible ->
    AyRestartMinState beforeFormula original beforeTrail :=
  fun formulaMap clauseMap resetForward resetBackward decode visibleProof =>
    ay_restart_min_equisat_backward
      (AyRestartMinState beforeFormula original beforeTrail)
      (AyRestartMinState afterFormula minimized afterTrail)
      (ay_restart_minimize_reset_inprocess_pipeline beforeFormula afterFormula
        beforeTrail afterTrail original minimized formulaMap clauseMap
        resetForward resetBackward)
      (decode visibleProof)
