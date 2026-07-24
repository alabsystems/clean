-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems bridging certified preprocessing maps to the global
-- solver-loop skeleton. The propositions stand for formula satisfiability,
-- solver outcomes, and proof-replay facts. Everything is Church encoded.

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyPreprocessMap (original : Prop) (preprocessed : Prop) :=
  AyEquisat original preprocessed

def AySolverSat (formula : Prop) (model : Prop) :=
  AyConj formula model

def AySolverUnsat (formula : Prop) (conflict : Prop) :=
  formula -> conflict

def AyProofReplay (formula : Prop) (certificate : Prop) (conflict : Prop) :=
  formula -> certificate -> conflict

def AyVisibleSolverBridge
    (original : Prop) (preprocessed : Prop)
    (outcome : Prop) (replay : Prop) :=
  AyConj original (AyConj preprocessed (AyConj outcome replay))

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

theorem ay_equisat_intro
    (original : Prop) (transformed : Prop) :
    (original -> transformed) ->
    (transformed -> original) ->
    AyEquisat original transformed := by
  intro forward
  intro backward
  exact ay_conj_intro
    (original -> transformed)
    (transformed -> original)
    forward
    backward

theorem ay_equisat_forward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    original -> transformed := by
  intro equisat
  exact ay_conj_left
    (original -> transformed)
    (transformed -> original)
    equisat

theorem ay_equisat_backward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    transformed -> original := by
  intro equisat
  exact ay_conj_right
    (original -> transformed)
    (transformed -> original)
    equisat

theorem ay_preprocess_feed_solver
    (original : Prop) (preprocessed : Prop) :
    AyPreprocessMap original preprocessed ->
    original ->
    preprocessed := by
  intro preprocess
  exact ay_equisat_forward original preprocessed preprocess

theorem ay_preprocess_reconstruct_model
    (original : Prop) (preprocessed : Prop) :
    AyPreprocessMap original preprocessed ->
    preprocessed ->
    original := by
  intro preprocess
  exact ay_equisat_backward original preprocessed preprocess

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

theorem ay_preprocessed_sat_reconstruct_original
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyPreprocessMap original preprocessed ->
    AySolverSat preprocessed model ->
    AySolverSat original model := by
  intro preprocess
  intro sat
  exact ay_conj_intro original model
    (ay_preprocess_reconstruct_model original preprocessed preprocess
      (ay_solver_sat_project_formula preprocessed model sat))
    (ay_solver_sat_project_model preprocessed model sat)

theorem ay_original_sat_feeds_preprocessed_solver
    (original : Prop) (preprocessed : Prop) (model : Prop) :
    AyPreprocessMap original preprocessed ->
    AySolverSat original model ->
    AySolverSat preprocessed model := by
  intro preprocess
  intro sat
  exact ay_conj_intro preprocessed model
    (ay_preprocess_feed_solver original preprocessed preprocess
      (ay_solver_sat_project_formula original model sat))
    (ay_solver_sat_project_model original model sat)

theorem ay_preprocessed_unsat_reconstruct_original
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AySolverUnsat preprocessed conflict ->
    AySolverUnsat original conflict := by
  intro preprocess
  intro unsat
  intro horiginal
  exact unsat
    (ay_preprocess_feed_solver original preprocessed preprocess horiginal)

theorem ay_original_unsat_projects_preprocessed
    (original : Prop) (preprocessed : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AySolverUnsat original conflict ->
    AySolverUnsat preprocessed conflict := by
  intro preprocess
  intro unsat
  intro hpreprocessed
  exact unsat
    (ay_preprocess_reconstruct_model original preprocessed preprocess
      hpreprocessed)

theorem ay_replay_valid_under_preprocess_projection
    (original : Prop) (preprocessed : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AyProofReplay preprocessed certificate conflict ->
    original ->
    certificate ->
    conflict := by
  intro preprocess
  intro replay
  intro horiginal
  intro hcertificate
  exact replay
    (ay_preprocess_feed_solver original preprocessed preprocess horiginal)
    hcertificate

theorem ay_replay_reconstructs_original_unsat
    (original : Prop) (preprocessed : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    AySolverUnsat original conflict := by
  intro preprocess
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_replay_valid_under_preprocess_projection
    original preprocessed certificate conflict
    preprocess replay horiginal hcertificate

theorem ay_visible_bridge_reconstruct
    (original : Prop) (preprocessed : Prop)
    (outcome : Prop) (replay : Prop) :
    original ->
    preprocessed ->
    outcome ->
    replay ->
    AyVisibleSolverBridge original preprocessed outcome replay := by
  intro horiginal
  intro hpreprocessed
  intro houtcome
  intro hreplay
  exact ay_conj_intro original
    (AyConj preprocessed (AyConj outcome replay))
    horiginal
    (ay_conj_intro preprocessed (AyConj outcome replay)
      hpreprocessed
      (ay_conj_intro outcome replay houtcome hreplay))

theorem ay_visible_bridge_project_original
    (original : Prop) (preprocessed : Prop)
    (outcome : Prop) (replay : Prop) :
    AyVisibleSolverBridge original preprocessed outcome replay ->
    original := by
  intro bridge
  exact ay_conj_left original
    (AyConj preprocessed (AyConj outcome replay))
    bridge

theorem ay_visible_bridge_project_preprocessed
    (original : Prop) (preprocessed : Prop)
    (outcome : Prop) (replay : Prop) :
    AyVisibleSolverBridge original preprocessed outcome replay ->
    preprocessed := by
  intro bridge
  exact ay_conj_left preprocessed (AyConj outcome replay)
    (ay_conj_right original
      (AyConj preprocessed (AyConj outcome replay))
      bridge)

theorem ay_visible_bridge_project_outcome
    (original : Prop) (preprocessed : Prop)
    (outcome : Prop) (replay : Prop) :
    AyVisibleSolverBridge original preprocessed outcome replay ->
    outcome := by
  intro bridge
  exact ay_conj_left outcome replay
    (ay_conj_right preprocessed (AyConj outcome replay)
      (ay_conj_right original
        (AyConj preprocessed (AyConj outcome replay))
        bridge))

theorem ay_visible_bridge_project_replay
    (original : Prop) (preprocessed : Prop)
    (outcome : Prop) (replay : Prop) :
    AyVisibleSolverBridge original preprocessed outcome replay ->
    replay := by
  intro bridge
  exact ay_conj_right outcome replay
    (ay_conj_right preprocessed (AyConj outcome replay)
      (ay_conj_right original
        (AyConj preprocessed (AyConj outcome replay))
        bridge))

theorem ay_preprocess_solver_sat_visible_forward
    (original : Prop) (preprocessed : Prop)
    (model : Prop) (replay : Prop) :
    AyPreprocessMap original preprocessed ->
    replay ->
    AySolverSat original model ->
    AyVisibleSolverBridge
      original
      preprocessed
      (AySolverSat preprocessed model)
      replay := by
  intro preprocess
  intro hreplay
  intro sat_original
  exact ay_visible_bridge_reconstruct
    original
    preprocessed
    (AySolverSat preprocessed model)
    replay
    (ay_solver_sat_project_formula original model sat_original)
    (ay_preprocess_feed_solver original preprocessed preprocess
      (ay_solver_sat_project_formula original model sat_original))
    (ay_original_sat_feeds_preprocessed_solver
      original preprocessed model preprocess sat_original)
    hreplay

theorem ay_preprocess_solver_sat_visible_backward
    (original : Prop) (preprocessed : Prop)
    (model : Prop) (replay : Prop) :
    AyPreprocessMap original preprocessed ->
    AyVisibleSolverBridge
      original
      preprocessed
      (AySolverSat preprocessed model)
      replay ->
    AySolverSat original model := by
  intro preprocess
  intro bridge
  exact ay_preprocessed_sat_reconstruct_original
    original preprocessed model preprocess
    (ay_visible_bridge_project_outcome
      original preprocessed (AySolverSat preprocessed model) replay bridge)

theorem ay_preprocess_solver_sat_visible_equisat
    (original : Prop) (preprocessed : Prop)
    (model : Prop) (replay : Prop) :
    AyPreprocessMap original preprocessed ->
    replay ->
    AyEquisat
      (AySolverSat original model)
      (AyVisibleSolverBridge
        original
        preprocessed
        (AySolverSat preprocessed model)
        replay) := by
  intro preprocess
  intro hreplay
  exact ay_equisat_intro
    (AySolverSat original model)
    (AyVisibleSolverBridge
      original
      preprocessed
      (AySolverSat preprocessed model)
      replay)
    (ay_preprocess_solver_sat_visible_forward
      original preprocessed model replay preprocess hreplay)
    (ay_preprocess_solver_sat_visible_backward
      original preprocessed model replay preprocess)

theorem ay_preprocess_solver_unsat_visible_forward
    (original : Prop) (preprocessed : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    original ->
    AyVisibleSolverBridge
      original
      preprocessed
      conflict
      (AyProofReplay preprocessed certificate conflict) := by
  intro preprocess
  intro replay
  intro hcertificate
  intro horiginal
  exact ay_visible_bridge_reconstruct
    original
    preprocessed
    conflict
    (AyProofReplay preprocessed certificate conflict)
    horiginal
    (ay_preprocess_feed_solver original preprocessed preprocess horiginal)
    (replay
      (ay_preprocess_feed_solver original preprocessed preprocess horiginal)
      hcertificate)
    replay

theorem ay_preprocess_solver_unsat_visible_backward
    (original : Prop) (preprocessed : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    AyVisibleSolverBridge
      original
      preprocessed
      conflict
      (AyProofReplay preprocessed certificate conflict) ->
    conflict := by
  intro _preprocess
  intro _replay
  intro _hcertificate
  intro bridge
  exact ay_visible_bridge_project_outcome
    original
    preprocessed
    conflict
    (AyProofReplay preprocessed certificate conflict)
    bridge

theorem ay_preprocess_solver_unsat_visible_equisat
    (original : Prop) (preprocessed : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessMap original preprocessed ->
    AyProofReplay preprocessed certificate conflict ->
    certificate ->
    AyEquisat
      original
      (AyVisibleSolverBridge
        original
        preprocessed
        conflict
        (AyProofReplay preprocessed certificate conflict)) := by
  intro preprocess
  intro replay
  intro hcertificate
  exact ay_equisat_intro
    original
    (AyVisibleSolverBridge
      original
      preprocessed
      conflict
      (AyProofReplay preprocessed certificate conflict))
    (ay_preprocess_solver_unsat_visible_forward
      original preprocessed certificate conflict
      preprocess replay hcertificate)
    (fun bridge =>
      ay_visible_bridge_project_original
        original preprocessed conflict
        (AyProofReplay preprocessed certificate conflict)
        bridge)
