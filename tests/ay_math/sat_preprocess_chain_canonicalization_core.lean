-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Canonical composition of SAT preprocessing chains. The propositions stand
-- for CNF satisfiability states, model payloads, replay certificates, and the
-- canonical artifact emitted after adjacent simplification passes are merged.

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

def AyPreprocessChain
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :=
  AyConj
    (AyEquisat originalCnf pass1Cnf)
    (AyConj
      (AyEquisat pass1Cnf pass2Cnf)
      (AyEquisat pass2Cnf visibleCnf))

def AyCanonicalArtifact (originalCnf : Prop) (visibleCnf : Prop) :=
  AyEquisat originalCnf visibleCnf

def AySatPullback (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyUnsatPushback
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)

def AyCanonicalCheckerContract
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyConj
    (AyCanonicalArtifact originalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))

def AyOutcomeContract
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  AyDisj
    (AySat originalCnf originalModel)
    (certificate -> originalCnf -> conflict)

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

theorem ay_chain_first_pass
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyEquisat originalCnf pass1Cnf := by
  intro chain
  exact ay_conj_left
    (AyEquisat originalCnf pass1Cnf)
    (AyConj
      (AyEquisat pass1Cnf pass2Cnf)
      (AyEquisat pass2Cnf visibleCnf))
    chain

theorem ay_chain_second_pass
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyEquisat pass1Cnf pass2Cnf := by
  intro chain
  exact ay_conj_left
    (AyEquisat pass1Cnf pass2Cnf)
    (AyEquisat pass2Cnf visibleCnf)
    (ay_conj_right
      (AyEquisat originalCnf pass1Cnf)
      (AyConj
        (AyEquisat pass1Cnf pass2Cnf)
        (AyEquisat pass2Cnf visibleCnf))
      chain)

theorem ay_chain_third_pass
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyEquisat pass2Cnf visibleCnf := by
  intro chain
  exact ay_conj_right
    (AyEquisat pass1Cnf pass2Cnf)
    (AyEquisat pass2Cnf visibleCnf)
    (ay_conj_right
      (AyEquisat originalCnf pass1Cnf)
      (AyConj
        (AyEquisat pass1Cnf pass2Cnf)
        (AyEquisat pass2Cnf visibleCnf))
      chain)

theorem ay_chain_original_to_pass2
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyEquisat originalCnf pass2Cnf := by
  intro chain
  exact ay_equisat_trans originalCnf pass1Cnf pass2Cnf
    (ay_chain_first_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)
    (ay_chain_second_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_chain_pass1_to_visible
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyEquisat pass1Cnf visibleCnf := by
  intro chain
  exact ay_equisat_trans pass1Cnf pass2Cnf visibleCnf
    (ay_chain_second_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)
    (ay_chain_third_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_chain_original_to_visible
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyEquisat originalCnf visibleCnf := by
  intro chain
  exact ay_equisat_trans originalCnf pass2Cnf visibleCnf
    (ay_chain_original_to_pass2
      originalCnf pass1Cnf pass2Cnf visibleCnf chain)
    (ay_chain_third_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_compress_first_two_passes
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyConj
      (AyEquisat originalCnf pass2Cnf)
      (AyEquisat pass2Cnf visibleCnf) := by
  intro chain
  exact ay_conj_intro
    (AyEquisat originalCnf pass2Cnf)
    (AyEquisat pass2Cnf visibleCnf)
    (ay_chain_original_to_pass2
      originalCnf pass1Cnf pass2Cnf visibleCnf chain)
    (ay_chain_third_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_compress_last_two_passes
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyConj
      (AyEquisat originalCnf pass1Cnf)
      (AyEquisat pass1Cnf visibleCnf) := by
  intro chain
  exact ay_conj_intro
    (AyEquisat originalCnf pass1Cnf)
    (AyEquisat pass1Cnf visibleCnf)
    (ay_chain_first_pass originalCnf pass1Cnf pass2Cnf visibleCnf chain)
    (ay_chain_pass1_to_visible
      originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_canonicalize_chain
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyCanonicalArtifact originalCnf visibleCnf := by
  exact ay_chain_original_to_visible originalCnf pass1Cnf pass2Cnf visibleCnf

theorem ay_canonical_forward
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    originalCnf ->
    visibleCnf := by
  exact ay_equisat_forward originalCnf visibleCnf

theorem ay_canonical_backward
    (originalCnf : Prop) (visibleCnf : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    visibleCnf ->
    originalCnf := by
  exact ay_equisat_backward originalCnf visibleCnf

theorem ay_chain_forward_matches_canonical
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    originalCnf ->
    visibleCnf := by
  intro chain
  exact ay_canonical_forward originalCnf visibleCnf
    (ay_canonicalize_chain originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_chain_backward_matches_canonical
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    visibleCnf ->
    originalCnf := by
  intro chain
  exact ay_canonical_backward originalCnf visibleCnf
    (ay_canonicalize_chain originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_canonical_visible_sat_pullback
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro canonical
  intro pullback
  intro sat
  exact ay_conj_intro originalCnf originalModel
    (ay_canonical_backward originalCnf visibleCnf canonical
      (ay_sat_cnf visibleCnf visibleModel sat))
    (pullback (ay_sat_model visibleCnf visibleModel sat))

theorem ay_chain_visible_sat_pullback
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro chain
  exact ay_canonical_visible_sat_pullback
    originalCnf visibleCnf visibleModel originalModel
    (ay_canonicalize_chain originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_canonical_unsat_pushback
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro canonical
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_canonical_forward originalCnf visibleCnf canonical horiginal)
    hcertificate

theorem ay_chain_unsat_pushback
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro chain
  exact ay_canonical_unsat_pushback
    originalCnf visibleCnf certificate conflict
    (ay_canonicalize_chain originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_canonical_unsat_pushback_artifact
    (originalCnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalArtifact originalCnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyUnsatPushback originalCnf visibleCnf certificate conflict := by
  intro canonical
  intro replay
  exact ay_conj_intro
    (originalCnf -> visibleCnf)
    (AyReplay visibleCnf certificate conflict)
    (ay_canonical_forward originalCnf visibleCnf canonical)
    replay

theorem ay_chain_unsat_pushback_artifact
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AyReplay visibleCnf certificate conflict ->
    AyUnsatPushback originalCnf visibleCnf certificate conflict := by
  intro chain
  exact ay_canonical_unsat_pushback_artifact
    originalCnf visibleCnf certificate conflict
    (ay_canonicalize_chain originalCnf pass1Cnf pass2Cnf visibleCnf chain)

theorem ay_canonical_contract_from_chain
    (originalCnf : Prop) (pass1Cnf : Prop)
    (pass2Cnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyPreprocessChain originalCnf pass1Cnf pass2Cnf visibleCnf ->
    AySatPullback visibleModel originalModel ->
    AyReplay visibleCnf certificate conflict ->
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict := by
  intro chain
  intro pullback
  intro replay
  exact ay_conj_intro
    (AyCanonicalArtifact originalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    (ay_canonicalize_chain originalCnf pass1Cnf pass2Cnf visibleCnf chain)
    (ay_conj_intro
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict)
      pullback
      replay)

theorem ay_canonical_contract_artifact
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyCanonicalArtifact originalCnf visibleCnf := by
  intro contract
  exact ay_conj_left
    (AyCanonicalArtifact originalCnf visibleCnf)
    (AyConj
      (AySatPullback visibleModel originalModel)
      (AyReplay visibleCnf certificate conflict))
    contract

theorem ay_canonical_contract_pullback
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySatPullback visibleModel originalModel := by
  intro contract
  exact ay_conj_left
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact originalCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_canonical_contract_replay
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyReplay visibleCnf certificate conflict := by
  intro contract
  exact ay_conj_right
    (AySatPullback visibleModel originalModel)
    (AyReplay visibleCnf certificate conflict)
    (ay_conj_right
      (AyCanonicalArtifact originalCnf visibleCnf)
      (AyConj
        (AySatPullback visibleModel originalModel)
        (AyReplay visibleCnf certificate conflict))
      contract)

theorem ay_canonical_contract_sat_obligation
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AySat originalCnf originalModel := by
  intro contract
  exact ay_canonical_visible_sat_pullback
    originalCnf visibleCnf visibleModel originalModel
    (ay_canonical_contract_artifact
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
    (ay_canonical_contract_pullback
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)

theorem ay_canonical_contract_unsat_obligation
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro contract
  exact ay_canonical_unsat_pushback
    originalCnf visibleCnf certificate conflict
    (ay_canonical_contract_artifact
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
    (ay_canonical_contract_replay
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)

theorem ay_outcome_contract_sat
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AySat originalCnf originalModel ->
    AyOutcomeContract originalCnf originalModel certificate conflict := by
  exact ay_disj_left
    (AySat originalCnf originalModel)
    (certificate -> originalCnf -> conflict)

theorem ay_outcome_contract_unsat
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    (certificate -> originalCnf -> conflict) ->
    AyOutcomeContract originalCnf originalModel certificate conflict := by
  exact ay_disj_right
    (AySat originalCnf originalModel)
    (certificate -> originalCnf -> conflict)

theorem ay_canonical_contract_sat_outcome
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AySat visibleCnf visibleModel ->
    AyOutcomeContract originalCnf originalModel certificate conflict := by
  intro contract
  intro sat
  exact ay_outcome_contract_sat
    originalCnf originalModel certificate conflict
    (ay_canonical_contract_sat_obligation
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract sat)

theorem ay_canonical_contract_unsat_outcome
    (originalCnf : Prop) (visibleCnf : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyCanonicalCheckerContract
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict ->
    AyOutcomeContract originalCnf originalModel certificate conflict := by
  intro contract
  exact ay_outcome_contract_unsat
    originalCnf originalModel certificate conflict
    (ay_canonical_contract_unsat_obligation
      originalCnf visibleCnf visibleModel originalModel
      certificate conflict contract)
