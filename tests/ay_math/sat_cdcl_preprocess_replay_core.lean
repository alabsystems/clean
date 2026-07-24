-- SAT-COMP CDCL + certified preprocessing + streaming replay core.
--
-- This file is intentionally abstract.  Formulas, learned databases, trails,
-- assignments, proof streams, and replay states are propositions.  Theorems
-- expose the forward/backward witnesses needed to connect a CDCL loop running
-- on a preprocessed formula with SAT model reconstruction and UNSAT proof
-- replay for the original formula.

def AyCPRConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCPRDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCPREquisat (before after : Prop) : Prop :=
  AyCPRConj (before -> after) (after -> before)

def AyCPRTransform (before after : Prop) : Prop :=
  AyCPREquisat before after

def AyCPRModel (formula assignment : Prop) : Prop :=
  AyCPRConj formula assignment

def AyCPRUnsat (formula : Prop) : Prop :=
  formula -> False

def AyCPROutcome (sat unsat : Prop) : Prop :=
  AyCPRDisj sat unsat

def AyCPRReplayState (formula stream : Prop) : Prop :=
  AyCPRConj formula stream

def AyCPRReplayCert (formula stream : Prop) : Prop :=
  stream -> formula -> False

def AyCPRStreamStep (before after : Prop) : Prop :=
  before -> after

def AyCPRCDCLState (formula learned trail decisions : Prop) : Prop :=
  AyCPRConj formula (AyCPRConj learned (AyCPRConj trail decisions))

def AyCPRCDCLSat (formula trail decisions assignment : Prop) : Prop :=
  AyCPRConj (AyCPRCDCLState formula formula trail decisions) assignment

def AyCPRCDCLUnsat (formula learned stream : Prop) : Prop :=
  AyCPRConj learned (AyCPRConj stream (AyCPRUnsat formula))

theorem ay_cpr_conj_intro (left right : Prop) :
    left -> right -> AyCPRConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cpr_conj_left (left right : Prop) :
    AyCPRConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cpr_conj_right (left right : Prop) :
    AyCPRConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cpr_disj_left (left right : Prop) :
    left -> AyCPRDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cpr_disj_right (left right : Prop) :
    right -> AyCPRDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cpr_equisat_forward (before after : Prop) :
    AyCPREquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_cpr_equisat_backward (before after : Prop) :
    AyCPREquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_cpr_equisat_refl (formula : Prop) :
    AyCPREquisat formula formula :=
  ay_cpr_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_cpr_equisat_symm (before after : Prop) :
    AyCPREquisat before after -> AyCPREquisat after before :=
  fun witness result build =>
    witness result (fun forward backward => build backward forward)

theorem ay_cpr_transform_compose (first second third : Prop) :
    AyCPRTransform first second ->
    AyCPRTransform second third ->
    AyCPRTransform first third :=
  fun leftStep rightStep result build =>
    leftStep result
      (fun leftForward leftBackward =>
        rightStep result
          (fun rightForward rightBackward =>
            build
              (fun hfirst => rightForward (leftForward hfirst))
              (fun hthird => leftBackward (rightBackward hthird))))

theorem ay_cpr_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyCPRModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_cpr_conj_intro formula assignment formulaProof assignmentProof

theorem ay_cpr_model_formula (formula assignment : Prop) :
    AyCPRModel formula assignment -> formula :=
  fun model => ay_cpr_conj_left formula assignment model

theorem ay_cpr_model_assignment (formula assignment : Prop) :
    AyCPRModel formula assignment -> assignment :=
  fun model => ay_cpr_conj_right formula assignment model

theorem ay_cpr_model_transport
    (beforeFormula afterFormula beforeAssignment afterAssignment : Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeAssignment -> afterAssignment) ->
    AyCPRModel beforeFormula beforeAssignment ->
    AyCPRModel afterFormula afterAssignment :=
  fun formulaForward assignmentForward model =>
    ay_cpr_model_intro afterFormula afterAssignment
      (formulaForward
        (ay_cpr_model_formula beforeFormula beforeAssignment model))
      (assignmentForward
        (ay_cpr_model_assignment beforeFormula beforeAssignment model))

theorem ay_cpr_model_reconstruct_through_preprocess
    (original preprocessed finalAssignment originalAssignment : Prop) :
    AyCPREquisat original preprocessed ->
    (finalAssignment -> originalAssignment) ->
    AyCPRModel preprocessed finalAssignment ->
    AyCPRModel original originalAssignment :=
  fun preprocessMap decodeAssignment model =>
    ay_cpr_model_transport preprocessed original finalAssignment
      originalAssignment
      (ay_cpr_equisat_backward original preprocessed preprocessMap)
      decodeAssignment model

theorem ay_cpr_unsat_transport_backward
    (original preprocessed : Prop) :
    AyCPREquisat original preprocessed ->
    AyCPRUnsat preprocessed ->
    AyCPRUnsat original :=
  fun preprocessMap unsat originalProof =>
    unsat (ay_cpr_equisat_forward original preprocessed preprocessMap
      originalProof)

theorem ay_cpr_unsat_transport_forward
    (original preprocessed : Prop) :
    AyCPREquisat original preprocessed ->
    AyCPRUnsat original ->
    AyCPRUnsat preprocessed :=
  fun preprocessMap unsat preprocessedProof =>
    unsat (ay_cpr_equisat_backward original preprocessed preprocessMap
      preprocessedProof)

theorem ay_cpr_replay_state_intro (formula stream : Prop) :
    formula -> stream -> AyCPRReplayState formula stream :=
  fun formulaProof streamProof =>
    ay_cpr_conj_intro formula stream formulaProof streamProof

theorem ay_cpr_replay_state_formula (formula stream : Prop) :
    AyCPRReplayState formula stream -> formula :=
  fun state => ay_cpr_conj_left formula stream state

theorem ay_cpr_replay_state_stream (formula stream : Prop) :
    AyCPRReplayState formula stream -> stream :=
  fun state => ay_cpr_conj_right formula stream state

theorem ay_cpr_replay_cert_sound
    (formula stream : Prop) :
    AyCPRReplayCert formula stream ->
    stream ->
    AyCPRUnsat formula :=
  fun cert streamProof formulaProof => cert streamProof formulaProof

theorem ay_cpr_replay_state_sound
    (formula stream : Prop) :
    AyCPRReplayCert formula stream ->
    AyCPRReplayState formula stream ->
    False :=
  fun cert state =>
    cert
      (ay_cpr_replay_state_stream formula stream state)
      (ay_cpr_replay_state_formula formula stream state)

theorem ay_cpr_stream_step_compose
    (first second third : Prop) :
    AyCPRStreamStep first second ->
    AyCPRStreamStep second third ->
    AyCPRStreamStep first third :=
  fun left right proof => right (left proof)

theorem ay_cpr_replay_cert_pullback_stream
    (formula beforeStream afterStream : Prop) :
    AyCPRStreamStep beforeStream afterStream ->
    AyCPRReplayCert formula afterStream ->
    AyCPRReplayCert formula beforeStream :=
  fun streamForward cert beforeStreamProof formulaProof =>
    cert (streamForward beforeStreamProof) formulaProof

theorem ay_cpr_replay_cert_transport_formula
    (beforeFormula afterFormula stream : Prop) :
    (beforeFormula -> afterFormula) ->
    AyCPRReplayCert afterFormula stream ->
    AyCPRReplayCert beforeFormula stream :=
  fun formulaForward cert streamProof beforeFormulaProof =>
    cert streamProof (formulaForward beforeFormulaProof)

theorem ay_cpr_streaming_replay_unsat
    (formula rawStream checkedStream : Prop) :
    AyCPRStreamStep rawStream checkedStream ->
    AyCPRReplayCert formula checkedStream ->
    rawStream ->
    AyCPRUnsat formula :=
  fun streamForward cert rawStreamProof =>
    ay_cpr_replay_cert_sound formula rawStream
      (ay_cpr_replay_cert_pullback_stream formula rawStream checkedStream
        streamForward cert)
      rawStreamProof

theorem ay_cpr_preprocess_streaming_replay_unsat
    (original preprocessed rawStream checkedStream : Prop) :
    AyCPREquisat original preprocessed ->
    AyCPRStreamStep rawStream checkedStream ->
    AyCPRReplayCert preprocessed checkedStream ->
    rawStream ->
    AyCPRUnsat original :=
  fun preprocessMap streamForward cert rawStreamProof =>
    ay_cpr_unsat_transport_backward original preprocessed preprocessMap
      (ay_cpr_streaming_replay_unsat preprocessed rawStream checkedStream
        streamForward cert rawStreamProof)

theorem ay_cpr_cdcl_state_intro
    (formula learned trail decisions : Prop) :
    formula -> learned -> trail -> decisions ->
    AyCPRCDCLState formula learned trail decisions :=
  fun formulaProof learnedProof trailProof decisionsProof =>
    ay_cpr_conj_intro formula
      (AyCPRConj learned (AyCPRConj trail decisions))
      formulaProof
      (ay_cpr_conj_intro learned (AyCPRConj trail decisions)
        learnedProof
        (ay_cpr_conj_intro trail decisions trailProof decisionsProof))

theorem ay_cpr_cdcl_state_formula
    (formula learned trail decisions : Prop) :
    AyCPRCDCLState formula learned trail decisions -> formula :=
  fun state => state formula (fun formulaProof _rest => formulaProof)

theorem ay_cpr_cdcl_state_learned
    (formula learned trail decisions : Prop) :
    AyCPRCDCLState formula learned trail decisions -> learned :=
  fun state =>
    state learned
      (fun _formulaProof rest =>
        rest learned (fun learnedProof _tail => learnedProof))

theorem ay_cpr_cdcl_state_trail
    (formula learned trail decisions : Prop) :
    AyCPRCDCLState formula learned trail decisions -> trail :=
  fun state =>
    state trail
      (fun _formulaProof rest =>
        rest trail
          (fun _learnedProof tail =>
            tail trail (fun trailProof _decisionsProof => trailProof)))

theorem ay_cpr_cdcl_state_decisions
    (formula learned trail decisions : Prop) :
    AyCPRCDCLState formula learned trail decisions -> decisions :=
  fun state =>
    state decisions
      (fun _formulaProof rest =>
        rest decisions
          (fun _learnedProof tail =>
            tail decisions (fun _trailProof decisionsProof => decisionsProof)))

theorem ay_cpr_preprocess_lifts_cdcl_state
    (original preprocessed learned trail decisions : Prop) :
    AyCPREquisat original preprocessed ->
    AyCPREquisat
      (AyCPRCDCLState original learned trail decisions)
      (AyCPRCDCLState preprocessed learned trail decisions) :=
  fun preprocessMap =>
    ay_cpr_conj_intro
      (AyCPRCDCLState original learned trail decisions ->
        AyCPRCDCLState preprocessed learned trail decisions)
      (AyCPRCDCLState preprocessed learned trail decisions ->
        AyCPRCDCLState original learned trail decisions)
      (fun state =>
        ay_cpr_cdcl_state_intro preprocessed learned trail decisions
          (ay_cpr_equisat_forward original preprocessed preprocessMap
            (ay_cpr_cdcl_state_formula original learned trail decisions
              state))
          (ay_cpr_cdcl_state_learned original learned trail decisions state)
          (ay_cpr_cdcl_state_trail original learned trail decisions state)
          (ay_cpr_cdcl_state_decisions original learned trail decisions state))
      (fun state =>
        ay_cpr_cdcl_state_intro original learned trail decisions
          (ay_cpr_equisat_backward original preprocessed preprocessMap
            (ay_cpr_cdcl_state_formula preprocessed learned trail decisions
              state))
          (ay_cpr_cdcl_state_learned preprocessed learned trail decisions
            state)
          (ay_cpr_cdcl_state_trail preprocessed learned trail decisions state)
          (ay_cpr_cdcl_state_decisions preprocessed learned trail decisions
            state))

theorem ay_cpr_cdcl_sat_to_model
    (formula trail decisions assignment : Prop) :
    AyCPRCDCLSat formula trail decisions assignment ->
    AyCPRModel formula assignment :=
  fun sat =>
    sat (AyCPRModel formula assignment)
      (fun state assignmentProof =>
        ay_cpr_model_intro formula assignment
          (ay_cpr_cdcl_state_formula formula formula trail decisions state)
          assignmentProof)

theorem ay_cpr_cdcl_unsat_to_unsat
    (formula learned stream : Prop) :
    AyCPRCDCLUnsat formula learned stream ->
    AyCPRUnsat formula :=
  fun cdclUnsat =>
    cdclUnsat (AyCPRUnsat formula)
      (fun _learnedProof tail =>
        tail (AyCPRUnsat formula)
          (fun _streamProof unsatProof => unsatProof))

theorem ay_cpr_cdcl_sat_reconstruct_original
    (original preprocessed trail decisions finalAssignment originalAssignment :
      Prop) :
    AyCPREquisat original preprocessed ->
    (finalAssignment -> originalAssignment) ->
    AyCPRCDCLSat preprocessed trail decisions finalAssignment ->
    AyCPRModel original originalAssignment :=
  fun preprocessMap decodeAssignment sat =>
    ay_cpr_model_reconstruct_through_preprocess original preprocessed
      finalAssignment originalAssignment preprocessMap decodeAssignment
      (ay_cpr_cdcl_sat_to_model preprocessed trail decisions finalAssignment
        sat)

theorem ay_cpr_cdcl_unsat_replay_original
    (original preprocessed learned rawStream checkedStream : Prop) :
    AyCPREquisat original preprocessed ->
    AyCPRStreamStep rawStream checkedStream ->
    AyCPRReplayCert preprocessed checkedStream ->
    rawStream ->
    AyCPRCDCLUnsat preprocessed learned checkedStream ->
    AyCPRUnsat original :=
  fun preprocessMap streamForward replayCert rawStreamProof _cdclUnsat =>
    ay_cpr_preprocess_streaming_replay_unsat original preprocessed rawStream
      checkedStream preprocessMap streamForward replayCert rawStreamProof

theorem ay_cpr_final_outcome_reconstruct
    (visibleSat visibleUnsat original preprocessed trail decisions
      finalAssignment originalAssignment learned rawStream checkedStream :
      Prop) :
    AyCPREquisat original preprocessed ->
    (finalAssignment -> originalAssignment) ->
    AyCPRStreamStep rawStream checkedStream ->
    AyCPRReplayCert preprocessed checkedStream ->
    rawStream ->
    (visibleSat -> AyCPRCDCLSat preprocessed trail decisions finalAssignment) ->
    (visibleUnsat ->
      AyCPRCDCLUnsat preprocessed learned checkedStream) ->
    AyCPROutcome visibleSat visibleUnsat ->
    AyCPROutcome
      (AyCPRModel original originalAssignment)
      (AyCPRUnsat original) :=
  fun preprocessMap decodeAssignment streamForward replayCert rawStreamProof
      decodeSat decodeUnsat outcome result onSat onUnsat =>
    outcome result
      (fun satProof =>
        onSat
          (ay_cpr_cdcl_sat_reconstruct_original original preprocessed trail
            decisions finalAssignment originalAssignment preprocessMap
            decodeAssignment (decodeSat satProof)))
      (fun unsatProof =>
        onUnsat
          (ay_cpr_cdcl_unsat_replay_original original preprocessed learned
            rawStream checkedStream preprocessMap streamForward replayCert
            rawStreamProof (decodeUnsat unsatProof)))
