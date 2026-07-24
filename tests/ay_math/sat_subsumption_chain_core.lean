-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for subsumption and self-subsuming resolution
-- chains. Clauses/formulas are propositions standing for model satisfaction.
-- Transformations are explicit Church-encoded forward/backward maps.

def AySubConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AySubDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AySubEquisat (before : Prop) (after : Prop) :=
  AySubConj (before -> after) (after -> before)

def AySubsumptionWitness (strongClause : Prop) (weakClause : Prop) :=
  strongClause -> weakClause

def AyStrengtheningWitness (strongerClause : Prop) (weakerClause : Prop) :=
  strongerClause -> weakerClause

def AySsrSideCondition (rest : Prop) (pivot : Prop) (tail : Prop) :=
  pivot -> rest -> tail

def AySubsumptionBefore
    (rest : Prop) (strongClause : Prop) (weakClause : Prop) :=
  AySubConj rest (AySubConj strongClause weakClause)

def AySubsumptionAfter
    (rest : Prop) (strongClause : Prop) :=
  AySubConj rest strongClause

def AyStrengtheningBefore
    (rest : Prop) (oldClause : Prop) :=
  AySubConj rest oldClause

def AyStrengtheningAfter
    (rest : Prop) (newClause : Prop) :=
  AySubConj rest newClause

def AySubSsrClause (pivot : Prop) (tail : Prop) :=
  AySubDisj pivot tail

def AySubChainStart
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) :=
  AySubConj rest
    (AySubConj strongClause (AySubConj weakClause oldClause))

def AySubChainMiddle
    (rest : Prop) (strongClause : Prop) (oldClause : Prop) :=
  AySubConj rest (AySubConj strongClause oldClause)

def AySubChainFinal
    (rest : Prop) (strongClause : Prop) (newClause : Prop) :=
  AySubConj rest (AySubConj strongClause newClause)

theorem ay_sub_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AySubConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_sub_disj_right
    (left : Prop) (right : Prop) :
    right -> AySubDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_sub_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AySubEquisat before after :=
  fun forward backward result keep =>
    keep forward backward

theorem ay_sub_equisat_forward
    (before : Prop) (after : Prop) :
    AySubEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_sub_equisat_backward
    (before : Prop) (after : Prop) :
    AySubEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_subsumption_delete_projection
    (rest : Prop) (strongClause : Prop) (weakClause : Prop) :
    AySubsumptionBefore rest strongClause weakClause ->
    AySubsumptionAfter rest strongClause :=
  fun before =>
    before (AySubsumptionAfter rest strongClause)
      (fun restH tail =>
        tail (AySubsumptionAfter rest strongClause)
          (fun strongH _weakH =>
            ay_sub_conj_intro rest strongClause restH strongH))

theorem ay_subsumption_delete_reconstruction
    (rest : Prop) (strongClause : Prop) (weakClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    AySubsumptionAfter rest strongClause ->
    AySubsumptionBefore rest strongClause weakClause :=
  fun subsumes after =>
    after (AySubsumptionBefore rest strongClause weakClause)
      (fun restH strongH =>
        ay_sub_conj_intro rest
          (AySubConj strongClause weakClause)
          restH
          (ay_sub_conj_intro strongClause weakClause
            strongH
            (subsumes strongH)))

theorem ay_subsumption_delete_equisat
    (rest : Prop) (strongClause : Prop) (weakClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    AySubEquisat
      (AySubsumptionBefore rest strongClause weakClause)
      (AySubsumptionAfter rest strongClause) :=
  fun subsumes =>
    ay_sub_equisat_intro
      (AySubsumptionBefore rest strongClause weakClause)
      (AySubsumptionAfter rest strongClause)
      (ay_subsumption_delete_projection
        rest strongClause weakClause)
      (ay_subsumption_delete_reconstruction
        rest strongClause weakClause subsumes)

theorem ay_self_subsuming_resolution_projection
    (rest : Prop) (pivot : Prop) (tail : Prop) :
    AySsrSideCondition rest pivot tail ->
    AyStrengtheningBefore rest (AySubSsrClause pivot tail) ->
    AyStrengtheningAfter rest tail :=
  fun side before =>
    before (AyStrengtheningAfter rest tail)
      (fun restH clause =>
        clause (AyStrengtheningAfter rest tail)
          (fun pivotH =>
            ay_sub_conj_intro rest tail restH
              (side pivotH restH))
          (fun tailH =>
            ay_sub_conj_intro rest tail restH tailH))

theorem ay_strengthening_projection
    (rest : Prop) (oldClause : Prop) (newClause : Prop) :
    (rest -> oldClause -> newClause) ->
    AyStrengtheningBefore rest oldClause ->
    AyStrengtheningAfter rest newClause :=
  fun strengthen before =>
    before (AyStrengtheningAfter rest newClause)
      (fun restH oldH =>
        ay_sub_conj_intro rest newClause
          restH
          (strengthen restH oldH))

theorem ay_strengthening_reconstruction
    (rest : Prop) (oldClause : Prop) (newClause : Prop) :
    AyStrengtheningWitness newClause oldClause ->
    AyStrengtheningAfter rest newClause ->
    AyStrengtheningBefore rest oldClause :=
  fun reconstruct after =>
    after (AyStrengtheningBefore rest oldClause)
      (fun restH newH =>
        ay_sub_conj_intro rest oldClause
          restH
          (reconstruct newH))

theorem ay_strengthening_equisat
    (rest : Prop) (oldClause : Prop) (newClause : Prop) :
    (rest -> oldClause -> newClause) ->
    AyStrengtheningWitness newClause oldClause ->
    AySubEquisat
      (AyStrengtheningBefore rest oldClause)
      (AyStrengtheningAfter rest newClause) :=
  fun strengthen reconstruct =>
    ay_sub_equisat_intro
      (AyStrengtheningBefore rest oldClause)
      (AyStrengtheningAfter rest newClause)
      (ay_strengthening_projection rest oldClause newClause strengthen)
      (ay_strengthening_reconstruction
        rest oldClause newClause reconstruct)

theorem ay_subsumption_chain_delete_projection
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) :
    AySubChainStart rest strongClause weakClause oldClause ->
    AySubChainMiddle rest strongClause oldClause :=
  fun start =>
    start (AySubChainMiddle rest strongClause oldClause)
      (fun restH tail =>
        tail (AySubChainMiddle rest strongClause oldClause)
          (fun strongH restTail =>
            restTail (AySubChainMiddle rest strongClause oldClause)
              (fun _weakH oldH =>
                ay_sub_conj_intro rest
                  (AySubConj strongClause oldClause)
                  restH
                  (ay_sub_conj_intro strongClause oldClause
                    strongH oldH))))

theorem ay_subsumption_chain_delete_reconstruction
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    AySubChainMiddle rest strongClause oldClause ->
    AySubChainStart rest strongClause weakClause oldClause :=
  fun subsumes middle =>
    middle (AySubChainStart rest strongClause weakClause oldClause)
      (fun restH tail =>
        tail (AySubChainStart rest strongClause weakClause oldClause)
          (fun strongH oldH =>
            ay_sub_conj_intro rest
              (AySubConj strongClause
                (AySubConj weakClause oldClause))
              restH
              (ay_sub_conj_intro strongClause
                (AySubConj weakClause oldClause)
                strongH
                (ay_sub_conj_intro weakClause oldClause
                  (subsumes strongH)
                  oldH))))

theorem ay_subsumption_chain_strengthen_projection
    (rest : Prop) (strongClause : Prop)
    (oldClause : Prop) (newClause : Prop) :
    (rest -> strongClause -> oldClause -> newClause) ->
    AySubChainMiddle rest strongClause oldClause ->
    AySubChainFinal rest strongClause newClause :=
  fun strengthen middle =>
    middle (AySubChainFinal rest strongClause newClause)
      (fun restH tail =>
        tail (AySubChainFinal rest strongClause newClause)
          (fun strongH oldH =>
            ay_sub_conj_intro rest
              (AySubConj strongClause newClause)
              restH
              (ay_sub_conj_intro strongClause newClause
                strongH
                (strengthen restH strongH oldH))))

theorem ay_subsumption_chain_strengthen_reconstruction
    (rest : Prop) (strongClause : Prop)
    (oldClause : Prop) (newClause : Prop) :
    AyStrengtheningWitness newClause oldClause ->
    AySubChainFinal rest strongClause newClause ->
    AySubChainMiddle rest strongClause oldClause :=
  fun reconstruct finalH =>
    finalH (AySubChainMiddle rest strongClause oldClause)
      (fun restH tail =>
        tail (AySubChainMiddle rest strongClause oldClause)
          (fun strongH newH =>
            ay_sub_conj_intro rest
              (AySubConj strongClause oldClause)
              restH
              (ay_sub_conj_intro strongClause oldClause
                strongH
                (reconstruct newH))))

theorem ay_subsumption_chain_projection
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) (newClause : Prop) :
    (rest -> strongClause -> oldClause -> newClause) ->
    AySubChainStart rest strongClause weakClause oldClause ->
    AySubChainFinal rest strongClause newClause :=
  fun strengthen start =>
    ay_subsumption_chain_strengthen_projection
      rest strongClause oldClause newClause strengthen
      (ay_subsumption_chain_delete_projection
        rest strongClause weakClause oldClause start)

theorem ay_subsumption_chain_reconstruction
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) (newClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    AyStrengtheningWitness newClause oldClause ->
    AySubChainFinal rest strongClause newClause ->
    AySubChainStart rest strongClause weakClause oldClause :=
  fun subsumes reconstruct finalH =>
    ay_subsumption_chain_delete_reconstruction
      rest strongClause weakClause oldClause subsumes
      (ay_subsumption_chain_strengthen_reconstruction
        rest strongClause oldClause newClause reconstruct finalH)

theorem ay_subsumption_chain_equisat
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) (newClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    (rest -> strongClause -> oldClause -> newClause) ->
    AyStrengtheningWitness newClause oldClause ->
    AySubEquisat
      (AySubChainStart rest strongClause weakClause oldClause)
      (AySubChainFinal rest strongClause newClause) :=
  fun subsumes strengthen reconstruct =>
    ay_sub_equisat_intro
      (AySubChainStart rest strongClause weakClause oldClause)
      (AySubChainFinal rest strongClause newClause)
      (ay_subsumption_chain_projection
        rest strongClause weakClause oldClause newClause strengthen)
      (ay_subsumption_chain_reconstruction
        rest strongClause weakClause oldClause newClause
        subsumes reconstruct)

theorem ay_subsumption_chain_preserves_forward_sat
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) (newClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    (rest -> strongClause -> oldClause -> newClause) ->
    AyStrengtheningWitness newClause oldClause ->
    AySubChainStart rest strongClause weakClause oldClause ->
    AySubChainFinal rest strongClause newClause :=
  fun subsumes strengthen reconstruct start =>
    ay_sub_equisat_forward
      (AySubChainStart rest strongClause weakClause oldClause)
      (AySubChainFinal rest strongClause newClause)
      (ay_subsumption_chain_equisat
        rest strongClause weakClause oldClause newClause
        subsumes strengthen reconstruct)
      start

theorem ay_subsumption_chain_preserves_backward_sat
    (rest : Prop) (strongClause : Prop)
    (weakClause : Prop) (oldClause : Prop) (newClause : Prop) :
    AySubsumptionWitness strongClause weakClause ->
    (rest -> strongClause -> oldClause -> newClause) ->
    AyStrengtheningWitness newClause oldClause ->
    AySubChainFinal rest strongClause newClause ->
    AySubChainStart rest strongClause weakClause oldClause :=
  fun subsumes strengthen reconstruct finalH =>
    ay_sub_equisat_backward
      (AySubChainStart rest strongClause weakClause oldClause)
      (AySubChainFinal rest strongClause newClause)
      (ay_subsumption_chain_equisat
        rest strongClause weakClause oldClause newClause
        subsumes strengthen reconstruct)
      finalH
