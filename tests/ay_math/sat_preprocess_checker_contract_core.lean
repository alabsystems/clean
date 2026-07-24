-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Preprocessing checker contract for SAT-COMP certificates. The propositions
-- stand for original/internal/visible CNF satisfiability, model payloads,
-- checker acceptance, replay certificates, and final contradictions.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyTransformSequence
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyEquisat originalCnf internalCnf)
    (AyEquisat internalCnf visibleCnf)

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatPushback
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)

def AyPreprocessCheckerAccepted
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyTransformSequence originalCnf internalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

def AySatCertificateContract
    (originalCnf : Prop) (originalModel : Prop) :=
  AySat originalCnf originalModel

def AyUnsatCertificateContract
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop) :=
  certificate -> originalCnf -> conflict

def AyCheckerOutcomeContract
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyDisj
    (AySatCertificateContract originalCnf originalModel)
    (AyUnsatCertificateContract originalCnf certificate conflict)

theorem ay_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_conj_left (before -> after) (after -> before) eq

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_conj_right (before -> after) (after -> before) eq

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (fun hfirst =>
      ay_equisat_forward middle last middle_last
        (ay_equisat_forward first middle first_middle hfirst))
    (fun hlast =>
      ay_equisat_backward first middle first_middle
        (ay_equisat_backward middle last middle_last hlast))

theorem ay_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_conj_left cnf model sat

theorem ay_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_conj_right cnf model sat

theorem ay_sequence_original_internal
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyTransformSequence originalCnf internalCnf visibleCnf ->
    AyEquisat originalCnf internalCnf := by
  intro sequence
  exact ay_conj_left
    (AyEquisat originalCnf internalCnf)
    (AyEquisat internalCnf visibleCnf)
    sequence

theorem ay_sequence_internal_visible
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyTransformSequence originalCnf internalCnf visibleCnf ->
    AyEquisat internalCnf visibleCnf := by
  intro sequence
  exact ay_conj_right
    (AyEquisat originalCnf internalCnf)
    (AyEquisat internalCnf visibleCnf)
    sequence

theorem ay_sequence_original_visible
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop) :
    AyTransformSequence originalCnf internalCnf visibleCnf ->
    AyEquisat originalCnf visibleCnf := by
  intro sequence
  exact ay_equisat_trans originalCnf internalCnf visibleCnf
    (ay_sequence_original_internal
      originalCnf internalCnf visibleCnf sequence)
    (ay_sequence_internal_visible
      originalCnf internalCnf visibleCnf sequence)

theorem ay_checker_sequence
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AyTransformSequence originalCnf internalCnf visibleCnf := by
  intro accepted
  exact ay_conj_left
    (AyTransformSequence originalCnf internalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    accepted

theorem ay_checker_sat_pullback
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AySatPullback visibleModel originalModel := by
  intro accepted
  exact ay_conj_left
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyTransformSequence originalCnf internalCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      accepted)

theorem ay_checker_visible_replay
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AyReplay visibleCnf certificate conflict := by
  intro accepted
  exact ay_conj_right
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyTransformSequence originalCnf internalCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      accepted)

theorem ay_checker_original_to_internal
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    originalCnf ->
    internalCnf := by
  intro accepted
  exact ay_equisat_forward originalCnf internalCnf
    (ay_sequence_original_internal originalCnf internalCnf visibleCnf
      (ay_checker_sequence
        originalCnf internalCnf visibleCnf
        visibleModel originalModel certificate conflict accepted))

theorem ay_checker_internal_to_original
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    internalCnf ->
    originalCnf := by
  intro accepted
  exact ay_equisat_backward originalCnf internalCnf
    (ay_sequence_original_internal originalCnf internalCnf visibleCnf
      (ay_checker_sequence
        originalCnf internalCnf visibleCnf
        visibleModel originalModel certificate conflict accepted))

theorem ay_checker_internal_to_visible
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    internalCnf ->
    visibleCnf := by
  intro accepted
  exact ay_equisat_forward internalCnf visibleCnf
    (ay_sequence_internal_visible originalCnf internalCnf visibleCnf
      (ay_checker_sequence
        originalCnf internalCnf visibleCnf
        visibleModel originalModel certificate conflict accepted))

theorem ay_checker_visible_to_internal
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    visibleCnf ->
    internalCnf := by
  intro accepted
  exact ay_equisat_backward internalCnf visibleCnf
    (ay_sequence_internal_visible originalCnf internalCnf visibleCnf
      (ay_checker_sequence
        originalCnf internalCnf visibleCnf
        visibleModel originalModel certificate conflict accepted))

theorem ay_checker_original_to_visible
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    originalCnf ->
    visibleCnf := by
  intro accepted
  intro horiginal
  exact ay_checker_internal_to_visible
    originalCnf internalCnf visibleCnf
    visibleModel originalModel certificate conflict accepted
    (ay_checker_original_to_internal
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted horiginal)

theorem ay_checker_visible_to_original
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    visibleCnf ->
    originalCnf := by
  intro accepted
  intro hvisible
  exact ay_checker_internal_to_original
    originalCnf internalCnf visibleCnf
    visibleModel originalModel certificate conflict accepted
    (ay_checker_visible_to_internal
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted hvisible)

theorem ay_checker_internal_sat_to_visible_sat
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AySat internalCnf visibleModel ->
    AySat visibleCnf visibleModel := by
  intro accepted
  intro sat
  exact ay_conj_intro visibleCnf visibleModel
    (ay_checker_internal_to_visible
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted
      (ay_sat_cnf internalCnf visibleModel sat))
    (ay_sat_model internalCnf visibleModel sat)

theorem ay_checker_visible_sat_to_original_sat
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AySat visibleCnf visibleModel ->
    AySatCertificateContract originalCnf originalModel := by
  intro accepted
  intro sat
  exact ay_conj_intro originalCnf originalModel
    (ay_checker_visible_to_original
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted
      (ay_sat_cnf visibleCnf visibleModel sat))
    (ay_checker_sat_pullback
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted
      (ay_sat_model visibleCnf visibleModel sat))

theorem ay_checker_internal_sat_pullback_contract
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AySat internalCnf visibleModel ->
    AySatCertificateContract originalCnf originalModel := by
  intro accepted
  intro sat
  exact ay_checker_visible_sat_to_original_sat
    originalCnf internalCnf visibleCnf
    visibleModel originalModel certificate conflict accepted
    (ay_checker_internal_sat_to_visible_sat
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted sat)

theorem ay_checker_unsat_pushback
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AyUnsatPushback originalCnf visibleCnf certificate conflict := by
  intro accepted
  exact ay_conj_intro
    (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    (ay_checker_original_to_visible
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted)
    (ay_checker_visible_replay
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted)

theorem ay_unsat_pushback_original_to_visible
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyUnsatPushback originalCnf visibleCnf certificate conflict ->
    originalCnf ->
    visibleCnf := by
  intro pushback
  exact ay_conj_left
    (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    pushback

theorem ay_unsat_pushback_replay
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyUnsatPushback originalCnf visibleCnf certificate conflict ->
    AyReplay visibleCnf certificate conflict := by
  intro pushback
  exact ay_conj_right
    (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    pushback

theorem ay_checker_unsat_contract
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AyUnsatCertificateContract originalCnf certificate conflict := by
  intro accepted
  intro hcertificate
  intro horiginal
  exact ay_unsat_pushback_replay originalCnf visibleCnf certificate conflict
    (ay_checker_unsat_pushback
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted)
    (ay_unsat_pushback_original_to_visible
      originalCnf visibleCnf certificate conflict
      (ay_checker_unsat_pushback
        originalCnf internalCnf visibleCnf
        visibleModel originalModel certificate conflict accepted)
      horiginal)
    hcertificate

theorem ay_checker_outcome_sat
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AySatCertificateContract originalCnf originalModel ->
    AyCheckerOutcomeContract
      originalCnf originalModel certificate conflict := by
  exact ay_disj_left
    (AySatCertificateContract originalCnf originalModel)
    (AyUnsatCertificateContract originalCnf certificate conflict)

theorem ay_checker_outcome_unsat
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyUnsatCertificateContract originalCnf certificate conflict ->
    AyCheckerOutcomeContract
      originalCnf originalModel certificate conflict := by
  exact ay_disj_right
    (AySatCertificateContract originalCnf originalModel)
    (AyUnsatCertificateContract originalCnf certificate conflict)

theorem ay_checker_acceptance_sat_outcome
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AySat internalCnf visibleModel ->
    AyCheckerOutcomeContract
      originalCnf originalModel certificate conflict := by
  intro accepted
  intro sat
  exact ay_checker_outcome_sat
    originalCnf originalModel certificate conflict
    (ay_checker_internal_sat_pullback_contract
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted sat)

theorem ay_checker_acceptance_unsat_outcome
    (originalCnf : Prop) (internalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessCheckerAccepted
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict ->
    AyCheckerOutcomeContract
      originalCnf originalModel certificate conflict := by
  intro accepted
  exact ay_checker_outcome_unsat
    originalCnf originalModel certificate conflict
    (ay_checker_unsat_contract
      originalCnf internalCnf visibleCnf
      visibleModel originalModel certificate conflict accepted)
