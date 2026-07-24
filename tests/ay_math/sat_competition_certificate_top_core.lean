-- SAT-COMP certificate top theorem.
--
-- This self-contained package is the highest-level abstract certificate shape:
-- preprocessing maps an original formula to a solver formula, CDCL produces a
-- visible SAT/UNSAT branch, proof replay certifies UNSAT streams, and the final
-- result is transported back to visible variables of the original instance.

def AyCCTConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCCTDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCCTEquisat (before after : Prop) : Prop :=
  AyCCTConj (before -> after) (after -> before)

def AyCCTModel (formula assignment : Prop) : Prop :=
  AyCCTConj formula assignment

def AyCCTUnsat (formula : Prop) : Prop :=
  formula -> False

def AyCCTOutcome (sat unsat : Prop) : Prop :=
  AyCCTDisj sat unsat

def AyCCTReplayCert (formula stream : Prop) : Prop :=
  stream -> formula -> False

def AyCCTCDCLSat (formula internalAssignment : Prop) : Prop :=
  AyCCTModel formula internalAssignment

def AyCCTCDCLUnsat (formula stream : Prop) : Prop :=
  AyCCTConj stream (AyCCTUnsat formula)

def AyCCTVisibleResult (original visibleAssignment : Prop) : Prop :=
  AyCCTModel original visibleAssignment

theorem ay_cct_conj_intro (left right : Prop) :
    left -> right -> AyCCTConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cct_conj_left (left right : Prop) :
    AyCCTConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cct_conj_right (left right : Prop) :
    AyCCTConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cct_disj_left (left right : Prop) :
    left -> AyCCTDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cct_disj_right (left right : Prop) :
    right -> AyCCTDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cct_equisat_forward (before after : Prop) :
    AyCCTEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_cct_equisat_backward (before after : Prop) :
    AyCCTEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_cct_equisat_refl (formula : Prop) :
    AyCCTEquisat formula formula :=
  ay_cct_conj_intro (formula -> formula) (formula -> formula)
    (fun h => h) (fun h => h)

theorem ay_cct_equisat_compose (first second third : Prop) :
    AyCCTEquisat first second ->
    AyCCTEquisat second third ->
    AyCCTEquisat first third :=
  fun leftStep rightStep result build =>
    leftStep result
      (fun leftForward leftBackward =>
        rightStep result
          (fun rightForward rightBackward =>
            build
              (fun hfirst => rightForward (leftForward hfirst))
              (fun hthird => leftBackward (rightBackward hthird))))

theorem ay_cct_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyCCTModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_cct_conj_intro formula assignment formulaProof assignmentProof

theorem ay_cct_model_formula (formula assignment : Prop) :
    AyCCTModel formula assignment -> formula :=
  fun model => ay_cct_conj_left formula assignment model

theorem ay_cct_model_assignment (formula assignment : Prop) :
    AyCCTModel formula assignment -> assignment :=
  fun model => ay_cct_conj_right formula assignment model

theorem ay_cct_model_transport
    (beforeFormula afterFormula beforeAssignment afterAssignment : Prop) :
    (beforeFormula -> afterFormula) ->
    (beforeAssignment -> afterAssignment) ->
    AyCCTModel beforeFormula beforeAssignment ->
    AyCCTModel afterFormula afterAssignment :=
  fun formulaMap assignmentMap model =>
    ay_cct_model_intro afterFormula afterAssignment
      (formulaMap
        (ay_cct_model_formula beforeFormula beforeAssignment model))
      (assignmentMap
        (ay_cct_model_assignment beforeFormula beforeAssignment model))

theorem ay_cct_preprocess_sat_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCCTEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCCTCDCLSat solver internalAssignment ->
    AyCCTVisibleResult original visibleAssignment :=
  fun preprocess decode sat =>
    ay_cct_model_transport solver original internalAssignment
      visibleAssignment
      (ay_cct_equisat_backward original solver preprocess)
      decode sat

theorem ay_cct_unsat_pullback_preprocess
    (original solver : Prop) :
    AyCCTEquisat original solver ->
    AyCCTUnsat solver ->
    AyCCTUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_cct_equisat_forward original solver preprocess originalProof)

theorem ay_cct_replay_sound (formula stream : Prop) :
    AyCCTReplayCert formula stream ->
    stream ->
    AyCCTUnsat formula :=
  fun cert streamProof formulaProof => cert streamProof formulaProof

theorem ay_cct_cdcl_unsat_stream (formula stream : Prop) :
    AyCCTCDCLUnsat formula stream -> stream :=
  fun unsatBranch =>
    ay_cct_conj_left stream (AyCCTUnsat formula) unsatBranch

theorem ay_cct_cdcl_unsat_claim (formula stream : Prop) :
    AyCCTCDCLUnsat formula stream -> AyCCTUnsat formula :=
  fun unsatBranch =>
    ay_cct_conj_right stream (AyCCTUnsat formula) unsatBranch

theorem ay_cct_replay_branch_unsat
    (formula stream : Prop) :
    AyCCTReplayCert formula stream ->
    AyCCTCDCLUnsat formula stream ->
    AyCCTUnsat formula :=
  fun cert branch =>
    ay_cct_replay_sound formula stream cert
      (ay_cct_cdcl_unsat_stream formula stream branch)

theorem ay_cct_replay_branch_agrees_with_cdcl
    (formula stream : Prop) :
    AyCCTReplayCert formula stream ->
    AyCCTCDCLUnsat formula stream ->
    AyCCTConj (AyCCTUnsat formula) (AyCCTUnsat formula) :=
  fun cert branch =>
    ay_cct_conj_intro (AyCCTUnsat formula) (AyCCTUnsat formula)
      (ay_cct_replay_branch_unsat formula stream cert branch)
      (ay_cct_cdcl_unsat_claim formula stream branch)

theorem ay_cct_preprocess_replay_unsat
    (original solver stream : Prop) :
    AyCCTEquisat original solver ->
    AyCCTReplayCert solver stream ->
    AyCCTCDCLUnsat solver stream ->
    AyCCTUnsat original :=
  fun preprocess cert branch =>
    ay_cct_unsat_pullback_preprocess original solver preprocess
      (ay_cct_replay_branch_unsat solver stream cert branch)

theorem ay_cct_outcome_transport
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyCCTOutcome beforeSat beforeUnsat ->
    AyCCTOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_cct_visible_sat_branch_sound
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCCTEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCCTCDCLSat solver internalAssignment ->
    AyCCTOutcome
      (AyCCTVisibleResult original visibleAssignment)
      (AyCCTUnsat original) :=
  fun preprocess decode sat =>
    ay_cct_disj_left
      (AyCCTVisibleResult original visibleAssignment)
      (AyCCTUnsat original)
      (ay_cct_preprocess_sat_reconstruct original solver
        internalAssignment visibleAssignment preprocess decode sat)

theorem ay_cct_visible_unsat_branch_sound
    (original solver stream visibleAssignment : Prop) :
    AyCCTEquisat original solver ->
    AyCCTReplayCert solver stream ->
    AyCCTCDCLUnsat solver stream ->
    AyCCTOutcome
      (AyCCTVisibleResult original visibleAssignment)
      (AyCCTUnsat original) :=
  fun preprocess cert branch =>
    ay_cct_disj_right
      (AyCCTVisibleResult original visibleAssignment)
      (AyCCTUnsat original)
      (ay_cct_preprocess_replay_unsat original solver stream preprocess cert
        branch)

theorem ay_cct_satcomp_certificate_top
    (visibleSat visibleUnsat original solver internalAssignment
      visibleAssignment stream : Prop) :
    AyCCTEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCCTReplayCert solver stream ->
    (visibleSat -> AyCCTCDCLSat solver internalAssignment) ->
    (visibleUnsat -> AyCCTCDCLUnsat solver stream) ->
    AyCCTOutcome visibleSat visibleUnsat ->
    AyCCTOutcome
      (AyCCTVisibleResult original visibleAssignment)
      (AyCCTUnsat original) :=
  fun preprocess decode replay decodeSat decodeUnsat outcome result onSat
      onUnsat =>
    outcome result
      (fun satProof =>
        onSat
          (ay_cct_preprocess_sat_reconstruct original solver
            internalAssignment visibleAssignment preprocess decode
            (decodeSat satProof)))
      (fun unsatProof =>
        onUnsat
          (ay_cct_preprocess_replay_unsat original solver stream preprocess
            replay (decodeUnsat unsatProof)))

theorem ay_cct_satcomp_certificate_top_from_cdcl_outcome
    (original solver internalAssignment visibleAssignment stream : Prop) :
    AyCCTEquisat original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCCTReplayCert solver stream ->
    AyCCTOutcome
      (AyCCTCDCLSat solver internalAssignment)
      (AyCCTCDCLUnsat solver stream) ->
    AyCCTOutcome
      (AyCCTVisibleResult original visibleAssignment)
      (AyCCTUnsat original) :=
  fun preprocess decode replay outcome =>
    ay_cct_satcomp_certificate_top
      (AyCCTCDCLSat solver internalAssignment)
      (AyCCTCDCLUnsat solver stream)
      original solver internalAssignment visibleAssignment stream
      preprocess decode replay (fun sat => sat) (fun unsat => unsat) outcome
