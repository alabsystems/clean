-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems fusing preprocessing master certificates, solver-loop
-- transport, and final SAT/UNSAT outcome reconstruction. The propositions
-- stand for formula satisfiability, solver models, conflicts, and certificates.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySolverSat (formula : Prop) (model : Prop) :=
  AyConj formula model

def AySolverUnsat (formula : Prop) (conflict : Prop) :=
  formula -> conflict

def AyProofReplay (formula : Prop) (certificate : Prop) (conflict : Prop) :=
  formula -> certificate -> conflict

def AyMasterPreprocessCertificate
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :=
  AyConj
    (AyEquisat original finalFormula)
    (AyEquisat finalFormula visibleFormula)

def AyFinalSatOutcome
    (original : Prop) (visibleFormula : Prop) (model : Prop) :=
  AyConj original (AyConj visibleFormula model)

def AyFinalUnsatOutcome
    (original : Prop) (visibleFormula : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj original (AyConj visibleFormula (AyConj certificate conflict))

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
    before -> after := by
  intro equisat
  exact ay_conj_left (before -> after) (after -> before) equisat

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after -> before := by
  intro equisat
  exact ay_conj_right (before -> after) (after -> before) equisat

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

theorem ay_master_project_internal
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyEquisat original finalFormula := by
  intro cert
  exact ay_conj_left
    (AyEquisat original finalFormula)
    (AyEquisat finalFormula visibleFormula)
    cert

theorem ay_master_project_visible
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyEquisat finalFormula visibleFormula := by
  intro cert
  exact ay_conj_right
    (AyEquisat original finalFormula)
    (AyEquisat finalFormula visibleFormula)
    cert

theorem ay_master_original_visible_equisat
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyEquisat original visibleFormula := by
  intro cert
  exact ay_equisat_trans original finalFormula visibleFormula
    (ay_master_project_internal original finalFormula visibleFormula cert)
    (ay_master_project_visible original finalFormula visibleFormula cert)

theorem ay_master_feed_solver
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    original ->
    finalFormula := by
  intro cert
  intro horiginal
  exact ay_equisat_forward original finalFormula
    (ay_master_project_internal original finalFormula visibleFormula cert)
    horiginal

theorem ay_master_reconstruct_original
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    finalFormula ->
    original := by
  intro cert
  intro hfinal
  exact ay_equisat_backward original finalFormula
    (ay_master_project_internal original finalFormula visibleFormula cert)
    hfinal

theorem ay_master_final_to_visible
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    finalFormula ->
    visibleFormula := by
  intro cert
  intro hfinal
  exact ay_equisat_forward finalFormula visibleFormula
    (ay_master_project_visible original finalFormula visibleFormula cert)
    hfinal

theorem ay_master_visible_to_final
    (original : Prop) (finalFormula : Prop) (visibleFormula : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    visibleFormula ->
    finalFormula := by
  intro cert
  intro hvisible
  exact ay_equisat_backward finalFormula visibleFormula
    (ay_master_project_visible original finalFormula visibleFormula cert)
    hvisible

theorem ay_solver_sat_project_formula
    (formula : Prop) (model : Prop) :
    AySolverSat formula model ->
    formula := by
  intro sat
  exact ay_conj_left formula model sat

theorem ay_solver_sat_project_model
    (formula : Prop) (model : Prop) :
    AySolverSat formula model ->
    model := by
  intro sat
  exact ay_conj_right formula model sat

theorem ay_sat_final_to_original_visible
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (model : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AySolverSat finalFormula model ->
    AyFinalSatOutcome original visibleFormula model := by
  intro cert
  intro sat
  exact ay_conj_intro original (AyConj visibleFormula model)
    (ay_master_reconstruct_original original finalFormula visibleFormula
      cert
      (ay_solver_sat_project_formula finalFormula model sat))
    (ay_conj_intro visibleFormula model
      (ay_master_final_to_visible original finalFormula visibleFormula
        cert
        (ay_solver_sat_project_formula finalFormula model sat))
      (ay_solver_sat_project_model finalFormula model sat))

theorem ay_sat_original_visible_to_final
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (model : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyFinalSatOutcome original visibleFormula model ->
    AySolverSat finalFormula model := by
  intro cert
  intro outcome
  exact ay_conj_intro finalFormula model
    (ay_master_visible_to_final original finalFormula visibleFormula cert
      (ay_conj_left visibleFormula model
        (ay_conj_right original (AyConj visibleFormula model)
          outcome)))
    (ay_conj_right visibleFormula model
      (ay_conj_right original (AyConj visibleFormula model)
        outcome))

theorem ay_sat_outcome_fusion_equisat
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (model : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyEquisat
      (AySolverSat finalFormula model)
      (AyFinalSatOutcome original visibleFormula model) := by
  intro cert
  exact ay_equisat_intro
    (AySolverSat finalFormula model)
    (AyFinalSatOutcome original visibleFormula model)
    (ay_sat_final_to_original_visible
      original finalFormula visibleFormula model cert)
    (ay_sat_original_visible_to_final
      original finalFormula visibleFormula model cert)

theorem ay_replay_final_unsat_to_original
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (certificate : Prop) (conflict : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyProofReplay finalFormula certificate conflict ->
    certificate ->
    original ->
    conflict := by
  intro cert
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_master_feed_solver original finalFormula visibleFormula cert
      horiginal)
    hcertificate

theorem ay_unsat_final_to_original_visible
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (certificate : Prop) (conflict : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyProofReplay finalFormula certificate conflict ->
    certificate ->
    original ->
    AyFinalUnsatOutcome original visibleFormula certificate conflict := by
  intro cert
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_conj_intro original
    (AyConj visibleFormula (AyConj certificate conflict))
    horiginal
    (ay_conj_intro visibleFormula (AyConj certificate conflict)
      (ay_equisat_forward original visibleFormula
        (ay_master_original_visible_equisat
          original finalFormula visibleFormula cert)
        horiginal)
      (ay_conj_intro certificate conflict
        hcertificate
        (ay_replay_final_unsat_to_original
          original finalFormula visibleFormula certificate conflict
          cert replay hcertificate horiginal)))

theorem ay_unsat_visible_to_conflict
    (original : Prop) (visibleFormula : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyFinalUnsatOutcome original visibleFormula certificate conflict ->
    conflict := by
  intro outcome
  exact ay_conj_right certificate conflict
    (ay_conj_right visibleFormula (AyConj certificate conflict)
      (ay_conj_right original
        (AyConj visibleFormula (AyConj certificate conflict))
        outcome))

theorem ay_unsat_visible_projects_original
    (original : Prop) (visibleFormula : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyFinalUnsatOutcome original visibleFormula certificate conflict ->
    original := by
  intro outcome
  exact ay_conj_left original
    (AyConj visibleFormula (AyConj certificate conflict))
    outcome

theorem ay_unsat_outcome_forward_map
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (certificate : Prop) (conflict : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyProofReplay finalFormula certificate conflict ->
    certificate ->
    original ->
    AyFinalUnsatOutcome original visibleFormula certificate conflict := by
  intro cert
  intro replay
  intro hcertificate
  exact ay_unsat_final_to_original_visible
    original finalFormula visibleFormula certificate conflict
    cert replay hcertificate

theorem ay_unsat_outcome_backward_map
    (original : Prop) (visibleFormula : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyFinalUnsatOutcome original visibleFormula certificate conflict ->
    original := by
  exact ay_unsat_visible_projects_original original visibleFormula
    certificate conflict

theorem ay_final_outcome_choice_forward_sat
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (model : Prop)
    (unsatOutcome : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyDisj (AySolverSat finalFormula model) unsatOutcome ->
    AyDisj (AyFinalSatOutcome original visibleFormula model) unsatOutcome := by
  intro cert
  intro choice
  intro result
  intro sat_case
  intro unsat_case
  exact choice result
    (fun sat_final =>
      sat_case
        (ay_sat_final_to_original_visible
          original finalFormula visibleFormula model cert sat_final))
    unsat_case

theorem ay_final_outcome_choice_backward_sat
    (original : Prop) (finalFormula : Prop)
    (visibleFormula : Prop) (model : Prop)
    (unsatOutcome : Prop) :
    AyMasterPreprocessCertificate original finalFormula visibleFormula ->
    AyDisj (AyFinalSatOutcome original visibleFormula model) unsatOutcome ->
    AyDisj (AySolverSat finalFormula model) unsatOutcome := by
  intro cert
  intro choice
  intro result
  intro sat_case
  intro unsat_case
  exact choice result
    (fun sat_original =>
      sat_case
        (ay_sat_original_visible_to_final
          original finalFormula visibleFormula model cert sat_original))
    unsat_case
