-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems composing binary implication SCC detection, backbone
-- discovery, and HBR-derived binary insertion. This package is self-contained
-- and uses Church-encoded conjunction, disjunction, and equisatisfiability.

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyEquiv (left : Prop) (right : Prop) :=
  AyConj (left -> right) (right -> left)

def AyBinaryImp (source : Prop) (target : Prop) :=
  AyDisj (Not source) target

def AyHbrParents (source : Prop) (middle : Prop) (target : Prop) :=
  AyConj (AyBinaryImp source middle) (AyBinaryImp middle target)

def AyWithDerived (context : Prop) (derived : Prop) :=
  AyConj context derived

def AyFormulaWithUnit (formula : Prop) (unitLit : Prop) :=
  AyConj formula unitLit

def AyBackboneLiteral (formula : Prop) (unitLit : Prop) :=
  formula -> unitLit

def AyFailedOppositeProbe (formula : Prop) (unitLit : Prop) :=
  formula -> unitLit

def AyBigBackboneContext
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :=
  AyConj formula (AyHbrParents source middle target)

def AyVisibleBackbonePipeline
    (original : Prop) (unitLit : Prop) (derivedBinary : Prop) :=
  AyConj original (AyConj unitLit derivedBinary)

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

theorem ay_equiv_forward
    (left : Prop) (right : Prop) :
    AyEquiv left right ->
    left -> right := by
  intro equiv
  exact ay_conj_left (left -> right) (right -> left) equiv

theorem ay_equiv_backward
    (left : Prop) (right : Prop) :
    AyEquiv left right ->
    right -> left := by
  intro equiv
  exact ay_conj_right (left -> right) (right -> left) equiv

theorem ay_binary_clause_to_implication
    (source : Prop) (target : Prop) :
    AyBinaryImp source target ->
    source ->
    target := by
  intro clause
  intro hsource
  exact clause target
    (fun not_source => False.elim (not_source hsource))
    (fun htarget => htarget)

theorem ay_mutual_implications_form_equiv
    (left : Prop) (right : Prop) :
    (left -> right) ->
    (right -> left) ->
    AyEquiv left right := by
  intro left_to_right
  intro right_to_left
  exact ay_conj_intro
    (left -> right)
    (right -> left)
    left_to_right
    right_to_left

theorem ay_scc_equiv_from_binary_implications
    (left : Prop) (right : Prop) :
    AyBinaryImp left right ->
    AyBinaryImp right left ->
    AyEquiv left right := by
  intro left_right
  intro right_left
  exact ay_mutual_implications_form_equiv left right
    (ay_binary_clause_to_implication left right left_right)
    (ay_binary_clause_to_implication right left right_left)

theorem ay_backbone_from_failed_probe
    (formula : Prop) (unitLit : Prop) :
    AyFailedOppositeProbe formula unitLit ->
    AyBackboneLiteral formula unitLit := by
  intro probe
  intro hformula
  exact probe hformula

theorem ay_backbone_transport_equiv_forward
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyEquiv oldLit newLit ->
    AyBackboneLiteral formula oldLit ->
    AyBackboneLiteral formula newLit := by
  intro lit_equiv
  intro backbone
  intro hformula
  exact ay_equiv_forward oldLit newLit lit_equiv
    (backbone hformula)

theorem ay_backbone_transport_equiv_backward
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyEquiv oldLit newLit ->
    AyBackboneLiteral formula newLit ->
    AyBackboneLiteral formula oldLit := by
  intro lit_equiv
  intro backbone
  intro hformula
  exact ay_equiv_backward oldLit newLit lit_equiv
    (backbone hformula)

theorem ay_formula_with_unit_add_forward
    (formula : Prop) (unitLit : Prop) :
    AyBackboneLiteral formula unitLit ->
    formula ->
    AyFormulaWithUnit formula unitLit := by
  intro backbone
  intro hformula
  exact ay_conj_intro formula unitLit
    hformula
    (backbone hformula)

theorem ay_formula_with_unit_add_backward
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    formula := by
  intro with_unit
  exact ay_conj_left formula unitLit with_unit

theorem ay_backbone_unit_add_equisat
    (formula : Prop) (unitLit : Prop) :
    AyBackboneLiteral formula unitLit ->
    AyEquisat formula (AyFormulaWithUnit formula unitLit) := by
  intro backbone
  exact ay_equisat_intro
    formula
    (AyFormulaWithUnit formula unitLit)
    (ay_formula_with_unit_add_forward formula unitLit backbone)
    (ay_formula_with_unit_add_backward formula unitLit)

theorem ay_hbr_binary_implication_transitive
    (source : Prop) (middle : Prop) (target : Prop) :
    AyBinaryImp source middle ->
    AyBinaryImp middle target ->
    AyBinaryImp source target := by
  intro source_middle
  intro middle_target
  intro result
  intro not_source_case
  intro target_case
  exact source_middle result
    not_source_case
    (fun hmiddle =>
      middle_target result
        (fun not_middle => False.elim (not_middle hmiddle))
        target_case)

theorem ay_hbr_parents_derive_binary
    (source : Prop) (middle : Prop) (target : Prop) :
    AyHbrParents source middle target ->
    AyBinaryImp source target := by
  intro parents
  exact parents (AyBinaryImp source target)
    (fun source_middle middle_target =>
      ay_hbr_binary_implication_transitive
        source middle target source_middle middle_target)

theorem ay_hbr_add_derived_forward
    (context : Prop) (derived : Prop) :
    (context -> derived) ->
    context ->
    AyWithDerived context derived := by
  intro derive
  intro hcontext
  exact ay_conj_intro context derived hcontext (derive hcontext)

theorem ay_hbr_add_derived_backward
    (context : Prop) (derived : Prop) :
    AyWithDerived context derived ->
    context := by
  intro with_derived
  exact ay_conj_left context derived with_derived

theorem ay_hbr_add_derived_equisat
    (context : Prop) (derived : Prop) :
    (context -> derived) ->
    AyEquisat context (AyWithDerived context derived) := by
  intro derive
  exact ay_equisat_intro
    context
    (AyWithDerived context derived)
    (ay_hbr_add_derived_forward context derived derive)
    (ay_hbr_add_derived_backward context derived)

theorem ay_big_context_project_formula
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyBigBackboneContext formula source middle target ->
    formula := by
  intro context
  exact ay_conj_left formula (AyHbrParents source middle target) context

theorem ay_big_context_project_hbr
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyBigBackboneContext formula source middle target ->
    AyHbrParents source middle target := by
  intro context
  exact ay_conj_right formula (AyHbrParents source middle target) context

theorem ay_big_pipeline_backbone_unit
    (formula : Prop) (oldLit : Prop) (newLit : Prop) :
    AyEquiv oldLit newLit ->
    AyFailedOppositeProbe formula oldLit ->
    formula ->
    AyFormulaWithUnit formula newLit := by
  intro lit_equiv
  intro probe
  exact ay_formula_with_unit_add_forward formula newLit
    (ay_backbone_transport_equiv_forward formula oldLit newLit
      lit_equiv
      (ay_backbone_from_failed_probe formula oldLit probe))

theorem ay_big_pipeline_derive_binary
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyBigBackboneContext formula source middle target ->
    AyBinaryImp source target := by
  intro context
  exact ay_hbr_parents_derive_binary source middle target
    (ay_big_context_project_hbr formula source middle target context)

theorem ay_big_pipeline_add_binary_forward
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyBigBackboneContext formula source middle target ->
    AyWithDerived
      (AyBigBackboneContext formula source middle target)
      (AyBinaryImp source target) := by
  intro context
  exact ay_hbr_add_derived_forward
    (AyBigBackboneContext formula source middle target)
    (AyBinaryImp source target)
    (ay_big_pipeline_derive_binary formula source middle target)
    context

theorem ay_big_pipeline_add_binary_backward
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyWithDerived
      (AyBigBackboneContext formula source middle target)
      (AyBinaryImp source target) ->
    AyBigBackboneContext formula source middle target := by
  intro with_derived
  exact ay_hbr_add_derived_backward
    (AyBigBackboneContext formula source middle target)
    (AyBinaryImp source target)
    with_derived

theorem ay_big_pipeline_add_binary_equisat
    (formula : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyEquisat
      (AyBigBackboneContext formula source middle target)
      (AyWithDerived
        (AyBigBackboneContext formula source middle target)
        (AyBinaryImp source target)) := by
  exact ay_hbr_add_derived_equisat
    (AyBigBackboneContext formula source middle target)
    (AyBinaryImp source target)
    (ay_big_pipeline_derive_binary formula source middle target)

theorem ay_visible_backbone_pipeline_reconstruct
    (original : Prop) (unitLit : Prop) (derivedBinary : Prop) :
    original ->
    unitLit ->
    derivedBinary ->
    AyVisibleBackbonePipeline original unitLit derivedBinary := by
  intro horiginal
  intro hunit
  intro hderived
  exact ay_conj_intro original (AyConj unitLit derivedBinary)
    horiginal
    (ay_conj_intro unitLit derivedBinary hunit hderived)

theorem ay_visible_backbone_pipeline_project_original
    (original : Prop) (unitLit : Prop) (derivedBinary : Prop) :
    AyVisibleBackbonePipeline original unitLit derivedBinary ->
    original := by
  intro visible
  exact visible original
    (fun horiginal _tail => horiginal)

theorem ay_visible_backbone_pipeline_project_unit
    (original : Prop) (unitLit : Prop) (derivedBinary : Prop) :
    AyVisibleBackbonePipeline original unitLit derivedBinary ->
    unitLit := by
  intro visible
  exact visible unitLit
    (fun _horiginal tail =>
      tail unitLit
        (fun hunit _hderived => hunit))

theorem ay_visible_backbone_pipeline_project_binary
    (original : Prop) (unitLit : Prop) (derivedBinary : Prop) :
    AyVisibleBackbonePipeline original unitLit derivedBinary ->
    derivedBinary := by
  intro visible
  exact visible derivedBinary
    (fun _horiginal tail =>
      tail derivedBinary
        (fun _hunit hderived => hderived))

theorem ay_big_pipeline_visible_forward
    (formula : Prop) (oldLit : Prop) (newLit : Prop)
    (source : Prop) (middle : Prop) (target : Prop) :
    AyEquiv oldLit newLit ->
    AyFailedOppositeProbe formula oldLit ->
    AyBigBackboneContext formula source middle target ->
    AyVisibleBackbonePipeline
      (AyBigBackboneContext formula source middle target)
      newLit
      (AyBinaryImp source target) := by
  intro lit_equiv
  intro probe
  intro context
  exact ay_visible_backbone_pipeline_reconstruct
    (AyBigBackboneContext formula source middle target)
    newLit
    (AyBinaryImp source target)
    context
    (ay_conj_right formula newLit
      (ay_big_pipeline_backbone_unit
        formula oldLit newLit lit_equiv probe
        (ay_big_context_project_formula
          formula source middle target context)))
    (ay_big_pipeline_derive_binary
      formula source middle target context)

theorem ay_big_pipeline_visible_backward
    (formula : Prop) (oldLit : Prop) (newLit : Prop)
    (source : Prop) (middle : Prop) (target : Prop) :
    AyVisibleBackbonePipeline
      (AyBigBackboneContext formula source middle target)
      newLit
      (AyBinaryImp source target) ->
    AyBigBackboneContext formula source middle target := by
  intro visible
  exact ay_visible_backbone_pipeline_project_original
    (AyBigBackboneContext formula source middle target)
    newLit
    (AyBinaryImp source target)
    visible

theorem ay_big_pipeline_visible_equisat
    (formula : Prop) (oldLit : Prop) (newLit : Prop)
    (source : Prop) (middle : Prop) (target : Prop) :
    AyEquiv oldLit newLit ->
    AyFailedOppositeProbe formula oldLit ->
    AyEquisat
      (AyBigBackboneContext formula source middle target)
      (AyVisibleBackbonePipeline
        (AyBigBackboneContext formula source middle target)
        newLit
        (AyBinaryImp source target)) := by
  intro lit_equiv
  intro probe
  exact ay_equisat_intro
    (AyBigBackboneContext formula source middle target)
    (AyVisibleBackbonePipeline
      (AyBigBackboneContext formula source middle target)
      newLit
      (AyBinaryImp source target))
    (ay_big_pipeline_visible_forward
      formula oldLit newLit source middle target lit_equiv probe)
    (ay_big_pipeline_visible_backward
      formula oldLit newLit source middle target)
