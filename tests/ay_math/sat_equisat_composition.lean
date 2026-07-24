-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked theorem-composition algebra for SAT-COMP-facing ay transformations.
-- The conjunction/equisatisfiability witnesses are Church encoded to stay on
-- clean's currently strongest proof-checking path. The names are prefixed
-- instead of namespaced because the current standalone checker handles
-- top-level declarations more reliably than namespace blocks.

def AySatEquisatConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AySatEquisat (original : Prop) (transformed : Prop) :=
  AySatEquisatConj (original -> transformed) (transformed -> original)

def AyPreprocessingTransform (before : Prop) (after : Prop) :=
  AySatEquisat before after

theorem ay_sat_equisat_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AySatEquisatConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_sat_equisat_conj_left
    (p : Prop) (q : Prop) :
    AySatEquisatConj p q -> p := by
  intro both
  exact both p (fun (hp : p) (_hq : q) => hp)

theorem ay_sat_equisat_refl
    (formula : Prop) :
    AySatEquisat formula formula := by
  exact ay_sat_equisat_conj_intro
    (formula -> formula)
    (formula -> formula)
    (fun hformula => hformula)
    (fun hformula => hformula)

theorem ay_sat_equisat_symm
    (original : Prop) (transformed : Prop) :
    AySatEquisat original transformed ->
    AySatEquisat transformed original := by
  intro witness
  intro result
  intro build
  exact witness result
    (fun forward backward =>
      build backward forward)

theorem ay_sat_equisat_forward_compose
    (original : Prop) (middle : Prop) (transformed : Prop) :
    AyPreprocessingTransform original middle ->
    AyPreprocessingTransform middle transformed ->
    original ->
    transformed :=
  fun first second horiginal =>
    first transformed
      (fun (first_forward : original -> middle)
           (_first_backward : middle -> original) =>
        second transformed
          (fun (second_forward : middle -> transformed)
               (_second_backward : transformed -> middle) =>
            second_forward (first_forward horiginal)))

theorem ay_sat_equisat_backward_compose
    (original : Prop) (middle : Prop) (transformed : Prop) :
    AyPreprocessingTransform original middle ->
    AyPreprocessingTransform middle transformed ->
    transformed ->
    original :=
  fun first second htransformed =>
    first original
      (fun (_first_forward : original -> middle)
           (first_backward : middle -> original) =>
        second original
          (fun (_second_forward : middle -> transformed)
               (second_backward : transformed -> middle) =>
            first_backward (second_backward htransformed)))

theorem ay_sat_equisat_trans
    (original : Prop) (middle : Prop) (transformed : Prop) :
    AyPreprocessingTransform original middle ->
    AyPreprocessingTransform middle transformed ->
    AyPreprocessingTransform original transformed :=
  fun first second result build =>
    first result
      (fun (first_forward : original -> middle)
           (first_backward : middle -> original) =>
        second result
          (fun (second_forward : middle -> transformed)
               (second_backward : transformed -> middle) =>
            build
              (fun horiginal => second_forward (first_forward horiginal))
              (fun htransformed => first_backward (second_backward htransformed))))

theorem ay_preprocessing_transforms_compose
    (input : Prop) (intermediate : Prop) (output : Prop) :
    AyPreprocessingTransform input intermediate ->
    AyPreprocessingTransform intermediate output ->
    AyPreprocessingTransform input output := by
  intro first_pass
  intro second_pass
  exact ay_sat_equisat_trans input intermediate output first_pass second_pass

theorem ay_preprocessing_composition_forward
    (input : Prop) (intermediate : Prop) (output : Prop) :
    AyPreprocessingTransform input intermediate ->
    AyPreprocessingTransform intermediate output ->
    input ->
    output := by
  intro first_pass
  intro second_pass
  intro hinput
  exact ay_sat_equisat_forward_compose
    input
    intermediate
    output
    first_pass
    second_pass
    hinput

theorem ay_preprocessing_composition_backward
    (input : Prop) (intermediate : Prop) (output : Prop) :
    AyPreprocessingTransform input intermediate ->
    AyPreprocessingTransform intermediate output ->
    output ->
    input := by
  intro first_pass
  intro second_pass
  intro houtput
  exact first_pass input
    (fun (_first_forward : input -> intermediate)
         (first_backward : intermediate -> input) =>
      second_pass input
        (fun (_second_forward : intermediate -> output)
             (second_backward : output -> intermediate) =>
          first_backward (second_backward houtput)))
