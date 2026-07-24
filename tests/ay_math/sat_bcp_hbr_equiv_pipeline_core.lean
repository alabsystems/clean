-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems composing BCP/unit propagation, HBR, and SCC
-- equivalence substitution. The package is self-contained and uses
-- Church-encoded conjunction, disjunction, and equisatisfiability.

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

def AyBcpHbrContext
    (unit : Prop) (source : Prop) (middle : Prop) (target : Prop) :=
  AyConj unit (AyHbrParents source middle target)

def AyVisiblePipelineTransport
    (original : Prop) (derived : Prop) (substituted : Prop) :=
  AyConj original (AyConj derived substituted)

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

theorem ay_bcp_unit_propagates_binary
    (unit : Prop) (target : Prop) :
    unit ->
    AyBinaryImp unit target ->
    target := by
  intro hunit
  intro clause
  exact ay_binary_clause_to_implication unit target clause hunit

theorem ay_bcp_binary_conflict
    (unit : Prop) :
    unit ->
    AyBinaryImp unit False ->
    False := by
  intro hunit
  intro conflict_clause
  exact ay_bcp_unit_propagates_binary unit False hunit conflict_clause

theorem ay_bcp_two_step_unit
    (first : Prop) (second : Prop) (third : Prop) :
    first ->
    AyBinaryImp first second ->
    AyBinaryImp second third ->
    third := by
  intro hfirst
  intro first_second
  intro second_third
  exact ay_bcp_unit_propagates_binary second third
    (ay_bcp_unit_propagates_binary first second hfirst first_second)
    second_third

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

theorem ay_binary_imp_substitute_target
    (source : Prop) (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyBinaryImp source target ->
    AyBinaryImp source targetSubst := by
  intro target_equiv
  intro clause
  intro result
  intro not_source_case
  intro target_subst_case
  exact clause result
    not_source_case
    (fun htarget =>
      target_subst_case
        (ay_equiv_forward target targetSubst target_equiv htarget))

theorem ay_binary_imp_reconstruct_target
    (source : Prop) (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyBinaryImp source targetSubst ->
    AyBinaryImp source target := by
  intro target_equiv
  intro clause
  intro result
  intro not_source_case
  intro target_case
  exact clause result
    not_source_case
    (fun htargetSubst =>
      target_case
        (ay_equiv_backward target targetSubst
          target_equiv htargetSubst))

theorem ay_hbr_scc_substitute_derived
    (source : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyHbrParents source middle target ->
    AyBinaryImp source targetSubst := by
  intro target_equiv
  intro parents
  exact ay_binary_imp_substitute_target source target targetSubst
    target_equiv
    (ay_hbr_parents_derive_binary source middle target parents)

theorem ay_pipeline_context_project_unit
    (unit : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyBcpHbrContext unit source middle target ->
    unit := by
  intro context
  exact ay_conj_left unit (AyHbrParents source middle target) context

theorem ay_pipeline_context_project_hbr
    (unit : Prop) (source : Prop) (middle : Prop) (target : Prop) :
    AyBcpHbrContext unit source middle target ->
    AyHbrParents source middle target := by
  intro context
  exact ay_conj_right unit (AyHbrParents source middle target) context

theorem ay_bcp_hbr_derive_substituted_unit
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyBcpHbrContext unit unit middle target ->
    targetSubst := by
  intro target_equiv
  intro context
  exact ay_bcp_unit_propagates_binary unit targetSubst
    (ay_pipeline_context_project_unit unit unit middle target context)
    (ay_hbr_scc_substitute_derived unit middle target targetSubst
      target_equiv
      (ay_pipeline_context_project_hbr unit unit middle target context))

theorem ay_pipeline_add_substituted_binary_forward
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyBcpHbrContext unit unit middle target ->
    AyWithDerived
      (AyBcpHbrContext unit unit middle target)
      (AyBinaryImp unit targetSubst) := by
  intro target_equiv
  exact ay_hbr_add_derived_forward
    (AyBcpHbrContext unit unit middle target)
    (AyBinaryImp unit targetSubst)
    (fun context =>
      ay_hbr_scc_substitute_derived unit middle target targetSubst
        target_equiv
        (ay_pipeline_context_project_hbr unit unit middle target context))

theorem ay_pipeline_add_substituted_binary_backward
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyWithDerived
      (AyBcpHbrContext unit unit middle target)
      (AyBinaryImp unit targetSubst) ->
    AyBcpHbrContext unit unit middle target := by
  intro with_derived
  exact ay_hbr_add_derived_backward
    (AyBcpHbrContext unit unit middle target)
    (AyBinaryImp unit targetSubst)
    with_derived

theorem ay_pipeline_add_substituted_binary_equisat
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyEquisat
      (AyBcpHbrContext unit unit middle target)
      (AyWithDerived
        (AyBcpHbrContext unit unit middle target)
        (AyBinaryImp unit targetSubst)) := by
  intro target_equiv
  exact ay_equisat_intro
    (AyBcpHbrContext unit unit middle target)
    (AyWithDerived
      (AyBcpHbrContext unit unit middle target)
      (AyBinaryImp unit targetSubst))
    (ay_pipeline_add_substituted_binary_forward
      unit middle target targetSubst target_equiv)
    (ay_pipeline_add_substituted_binary_backward
      unit middle target targetSubst)

theorem ay_visible_pipeline_reconstruct
    (original : Prop) (derived : Prop) (substituted : Prop) :
    original ->
    derived ->
    substituted ->
    AyVisiblePipelineTransport original derived substituted := by
  intro horiginal
  intro hderived
  intro hsubstituted
  exact ay_conj_intro original (AyConj derived substituted)
    horiginal
    (ay_conj_intro derived substituted hderived hsubstituted)

theorem ay_visible_pipeline_project_original
    (original : Prop) (derived : Prop) (substituted : Prop) :
    AyVisiblePipelineTransport original derived substituted ->
    original := by
  intro visible
  exact visible original
    (fun horiginal _tail => horiginal)

theorem ay_visible_pipeline_project_derived
    (original : Prop) (derived : Prop) (substituted : Prop) :
    AyVisiblePipelineTransport original derived substituted ->
    derived := by
  intro visible
  exact visible derived
    (fun _horiginal tail =>
      tail derived
        (fun hderived _hsubstituted => hderived))

theorem ay_visible_pipeline_project_substituted
    (original : Prop) (derived : Prop) (substituted : Prop) :
    AyVisiblePipelineTransport original derived substituted ->
    substituted := by
  intro visible
  exact visible substituted
    (fun _horiginal tail =>
      tail substituted
        (fun _hderived hsubstituted => hsubstituted))

theorem ay_pipeline_visible_transport_forward
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyBcpHbrContext unit unit middle target ->
    AyVisiblePipelineTransport
      (AyBcpHbrContext unit unit middle target)
      (AyBinaryImp unit target)
      (AyBinaryImp unit targetSubst) := by
  intro target_equiv
  intro context
  let derived :=
    ay_hbr_parents_derive_binary unit middle target
      (ay_pipeline_context_project_hbr unit unit middle target context)
  exact ay_visible_pipeline_reconstruct
    (AyBcpHbrContext unit unit middle target)
    (AyBinaryImp unit target)
    (AyBinaryImp unit targetSubst)
    context
    derived
    (ay_binary_imp_substitute_target unit target targetSubst
      target_equiv derived)

theorem ay_pipeline_visible_transport_backward
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyVisiblePipelineTransport
      (AyBcpHbrContext unit unit middle target)
      (AyBinaryImp unit target)
      (AyBinaryImp unit targetSubst) ->
    AyBcpHbrContext unit unit middle target := by
  intro visible
  exact ay_visible_pipeline_project_original
    (AyBcpHbrContext unit unit middle target)
    (AyBinaryImp unit target)
    (AyBinaryImp unit targetSubst)
    visible

theorem ay_pipeline_visible_transport_equisat
    (unit : Prop) (middle : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv target targetSubst ->
    AyEquisat
      (AyBcpHbrContext unit unit middle target)
      (AyVisiblePipelineTransport
        (AyBcpHbrContext unit unit middle target)
        (AyBinaryImp unit target)
        (AyBinaryImp unit targetSubst)) := by
  intro target_equiv
  exact ay_equisat_intro
    (AyBcpHbrContext unit unit middle target)
    (AyVisiblePipelineTransport
      (AyBcpHbrContext unit unit middle target)
      (AyBinaryImp unit target)
      (AyBinaryImp unit targetSubst))
    (ay_pipeline_visible_transport_forward
      unit middle target targetSubst target_equiv)
    (ay_pipeline_visible_transport_backward
      unit middle target targetSubst)
