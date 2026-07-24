-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for SAT preprocessing pipeline composition.
-- Formulas are propositions standing for "there exists a satisfying model".
-- A pipeline transform is equisatisfiability: a forward model map and a
-- backward reconstruction map, Church-encoded for clean's standalone checker.

def AyPipelineConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPipelineEquisat (before : Prop) (after : Prop) :=
  AyPipelineConj (before -> after) (after -> before)

def AyPipelineTransform (before : Prop) (after : Prop) :=
  AyPipelineEquisat before after

def AyPreprocessingPass (input : Prop) (preprocessed : Prop) :=
  AyPipelineTransform input preprocessed

def AyInprocessingPass (preprocessed : Prop) (inprocessed : Prop) :=
  AyPipelineTransform preprocessed inprocessed

def AyReconstructionPass (inprocessed : Prop) (reconstructed : Prop) :=
  AyPipelineTransform inprocessed reconstructed

theorem ay_pipeline_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPipelineConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_pipeline_forward_map
    (before : Prop) (after : Prop) :
    AyPipelineTransform before after -> before -> after := by
  intro transform
  exact transform (before -> after)
    (fun forward _backward => forward)

theorem ay_pipeline_backward_map
    (before : Prop) (after : Prop) :
    AyPipelineTransform before after -> after -> before := by
  intro transform
  exact transform (after -> before)
    (fun _forward backward => backward)

theorem ay_pipeline_three_forward_map
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop) (stage3 : Prop) :
    AyPipelineTransform stage0 stage1 ->
    AyPipelineTransform stage1 stage2 ->
    AyPipelineTransform stage2 stage3 ->
    stage0 ->
    stage3 :=
  fun first second third h0 =>
    first stage3
      (fun firstForward _firstBackward =>
        second stage3
          (fun secondForward _secondBackward =>
            third stage3
              (fun thirdForward _thirdBackward =>
                thirdForward (secondForward (firstForward h0)))))

theorem ay_pipeline_three_backward_map
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop) (stage3 : Prop) :
    AyPipelineTransform stage0 stage1 ->
    AyPipelineTransform stage1 stage2 ->
    AyPipelineTransform stage2 stage3 ->
    stage3 ->
    stage0 :=
  fun first second third h3 =>
    first stage0
      (fun _firstForward firstBackward =>
        second stage0
          (fun _secondForward secondBackward =>
            third stage0
              (fun _thirdForward thirdBackward =>
                firstBackward (secondBackward (thirdBackward h3)))))

theorem ay_pipeline_three_equisat
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop) (stage3 : Prop) :
    AyPipelineTransform stage0 stage1 ->
    AyPipelineTransform stage1 stage2 ->
    AyPipelineTransform stage2 stage3 ->
    AyPipelineTransform stage0 stage3 :=
  fun first second third result build =>
    first result
      (fun firstForward firstBackward =>
        second result
          (fun secondForward secondBackward =>
            third result
              (fun thirdForward thirdBackward =>
                build
                  (fun h0 => thirdForward (secondForward (firstForward h0)))
                  (fun h3 => firstBackward (secondBackward (thirdBackward h3))))))

theorem ay_sat_preprocess_inprocess_reconstruct_forward
    (original : Prop) (preprocessed : Prop)
    (inprocessed : Prop) (reconstructed : Prop) :
    AyPreprocessingPass original preprocessed ->
    AyInprocessingPass preprocessed inprocessed ->
    AyReconstructionPass inprocessed reconstructed ->
    original ->
    reconstructed := by
  intro preprocessing
  intro inprocessing
  intro reconstruction
  exact ay_pipeline_three_forward_map
    original preprocessed inprocessed reconstructed
    preprocessing inprocessing reconstruction

theorem ay_sat_preprocess_inprocess_reconstruct_backward
    (original : Prop) (preprocessed : Prop)
    (inprocessed : Prop) (reconstructed : Prop) :
    AyPreprocessingPass original preprocessed ->
    AyInprocessingPass preprocessed inprocessed ->
    AyReconstructionPass inprocessed reconstructed ->
    reconstructed ->
    original := by
  intro preprocessing
  intro inprocessing
  intro reconstruction
  exact ay_pipeline_three_backward_map
    original preprocessed inprocessed reconstructed
    preprocessing inprocessing reconstruction

theorem ay_sat_preprocess_inprocess_reconstruct_equisat
    (original : Prop) (preprocessed : Prop)
    (inprocessed : Prop) (reconstructed : Prop) :
    AyPreprocessingPass original preprocessed ->
    AyInprocessingPass preprocessed inprocessed ->
    AyReconstructionPass inprocessed reconstructed ->
    AyPipelineTransform original reconstructed := by
  intro preprocessing
  intro inprocessing
  intro reconstruction
  exact ay_pipeline_three_equisat
    original preprocessed inprocessed reconstructed
    preprocessing inprocessing reconstruction
