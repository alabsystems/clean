-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for binary implication graph SCC/equivalence
-- detection. The package is self-contained and uses Church encodings for
-- conjunction, disjunction, and equisatisfiability.

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

def AyMutualBinaryImp (left : Prop) (right : Prop) :=
  AyConj (AyBinaryImp left right) (AyBinaryImp right left)

def AyHbrParents (source : Prop) (middle : Prop) (target : Prop) :=
  AyConj (AyBinaryImp source middle) (AyBinaryImp middle target)

def AyWithDerived (context : Prop) (derived : Prop) :=
  AyConj context derived

def AyTwoBinaryContext
    (atom : Prop) (tailA : Prop) (tailB : Prop) :=
  AyConj (AyBinaryImp atom tailA) (AyBinaryImp tailB atom)

def AyVisibleSccTransport
    (original : Prop) (substituted : Prop) (witness : Prop) :=
  AyConj original (AyConj substituted witness)

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

theorem ay_equiv_trans
    (left : Prop) (middle : Prop) (right : Prop) :
    AyEquiv left middle ->
    AyEquiv middle right ->
    AyEquiv left right := by
  intro left_equiv_middle
  intro middle_equiv_right
  exact ay_mutual_implications_form_equiv left right
    (fun hleft =>
      ay_equiv_forward middle right middle_equiv_right
        (ay_equiv_forward left middle left_equiv_middle hleft))
    (fun hright =>
      ay_equiv_backward left middle left_equiv_middle
        (ay_equiv_backward middle right middle_equiv_right hright))

theorem ay_binary_imp_substitute_source
    (source : Prop) (sourceSubst : Prop) (target : Prop) :
    AyEquiv source sourceSubst ->
    AyBinaryImp source target ->
    AyBinaryImp sourceSubst target := by
  intro source_equiv
  intro clause
  intro result
  intro not_source_subst_case
  intro target_case
  exact clause result
    (fun not_source =>
      not_source_subst_case
        (fun hsource_subst =>
          not_source
            (ay_equiv_backward source sourceSubst
              source_equiv hsource_subst)))
    target_case

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

theorem ay_binary_imp_substitute_both
    (source : Prop) (sourceSubst : Prop)
    (target : Prop) (targetSubst : Prop) :
    AyEquiv source sourceSubst ->
    AyEquiv target targetSubst ->
    AyBinaryImp source target ->
    AyBinaryImp sourceSubst targetSubst := by
  intro source_equiv
  intro target_equiv
  intro clause
  exact ay_binary_imp_substitute_target sourceSubst target targetSubst
    target_equiv
    (ay_binary_imp_substitute_source
      source sourceSubst target source_equiv clause)

theorem ay_two_binary_context_substitute
    (atom : Prop) (atomSubst : Prop)
    (tailA : Prop) (tailB : Prop) :
    AyEquiv atom atomSubst ->
    AyTwoBinaryContext atom tailA tailB ->
    AyTwoBinaryContext atomSubst tailA tailB := by
  intro atom_equiv
  intro context
  intro result
  intro build
  exact context result
    (fun first second =>
      build
        (ay_binary_imp_substitute_source
          atom atomSubst tailA atom_equiv first)
        (ay_binary_imp_substitute_target
          tailB atom atomSubst atom_equiv second))

theorem ay_two_binary_context_reconstruct
    (atom : Prop) (atomSubst : Prop)
    (tailA : Prop) (tailB : Prop) :
    AyEquiv atom atomSubst ->
    AyTwoBinaryContext atomSubst tailA tailB ->
    AyTwoBinaryContext atom tailA tailB := by
  intro atom_equiv
  intro context
  intro result
  intro build
  exact context result
    (fun first second =>
      build
        (ay_binary_imp_substitute_source
          atomSubst atom tailA
          (ay_mutual_implications_form_equiv
            atomSubst atom
            (ay_equiv_backward atom atomSubst atom_equiv)
            (ay_equiv_forward atom atomSubst atom_equiv))
          first)
        (ay_binary_imp_substitute_target
          tailB atomSubst atom
          (ay_mutual_implications_form_equiv
            atomSubst atom
            (ay_equiv_backward atom atomSubst atom_equiv)
            (ay_equiv_forward atom atomSubst atom_equiv))
          second))

theorem ay_two_binary_context_equisat
    (atom : Prop) (atomSubst : Prop)
    (tailA : Prop) (tailB : Prop) :
    AyEquiv atom atomSubst ->
    AyEquisat
      (AyTwoBinaryContext atom tailA tailB)
      (AyTwoBinaryContext atomSubst tailA tailB) := by
  intro atom_equiv
  exact ay_equisat_intro
    (AyTwoBinaryContext atom tailA tailB)
    (AyTwoBinaryContext atomSubst tailA tailB)
    (ay_two_binary_context_substitute
      atom atomSubst tailA tailB atom_equiv)
    (ay_two_binary_context_reconstruct
      atom atomSubst tailA tailB atom_equiv)

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

theorem ay_hbr_scc_substitute_derived
    (source : Prop) (sourceSubst : Prop)
    (middle : Prop) (target : Prop) :
    AyEquiv source sourceSubst ->
    AyHbrParents source middle target ->
    AyBinaryImp sourceSubst target := by
  intro source_equiv
  intro parents
  exact ay_binary_imp_substitute_source source sourceSubst target
    source_equiv
    (ay_hbr_parents_derive_binary source middle target parents)

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

theorem ay_hbr_add_scc_substituted_binary_equisat
    (source : Prop) (sourceSubst : Prop)
    (middle : Prop) (target : Prop) :
    AyEquiv source sourceSubst ->
    AyEquisat
      (AyHbrParents source middle target)
      (AyWithDerived
        (AyHbrParents source middle target)
        (AyBinaryImp sourceSubst target)) := by
  intro source_equiv
  exact ay_equisat_intro
    (AyHbrParents source middle target)
    (AyWithDerived
      (AyHbrParents source middle target)
      (AyBinaryImp sourceSubst target))
    (ay_hbr_add_derived_forward
      (AyHbrParents source middle target)
      (AyBinaryImp sourceSubst target)
      (ay_hbr_scc_substitute_derived
        source sourceSubst middle target source_equiv))
    (ay_hbr_add_derived_backward
      (AyHbrParents source middle target)
      (AyBinaryImp sourceSubst target))

theorem ay_visible_transport_reconstruct
    (original : Prop) (substituted : Prop) (witness : Prop) :
    original ->
    substituted ->
    witness ->
    AyVisibleSccTransport original substituted witness := by
  intro horiginal
  intro hsubstituted
  intro hwitness
  exact ay_conj_intro original (AyConj substituted witness)
    horiginal
    (ay_conj_intro substituted witness hsubstituted hwitness)

theorem ay_visible_transport_project_original
    (original : Prop) (substituted : Prop) (witness : Prop) :
    AyVisibleSccTransport original substituted witness ->
    original := by
  intro visible
  exact visible original
    (fun horiginal _tail => horiginal)

theorem ay_visible_transport_project_substituted
    (original : Prop) (substituted : Prop) (witness : Prop) :
    AyVisibleSccTransport original substituted witness ->
    substituted := by
  intro visible
  exact visible substituted
    (fun _horiginal tail =>
      tail substituted
        (fun hsubstituted _hwitness => hsubstituted))

theorem ay_visible_transport_project_witness
    (original : Prop) (substituted : Prop) (witness : Prop) :
    AyVisibleSccTransport original substituted witness ->
    witness := by
  intro visible
  exact visible witness
    (fun _horiginal tail =>
      tail witness
        (fun _hsubstituted hwitness => hwitness))

theorem ay_scc_visible_model_transport
    (original : Prop) (substituted : Prop) (witness : Prop) :
    (original -> substituted) ->
    (substituted -> original) ->
    (original -> witness) ->
    AyEquisat
      original
      (AyVisibleSccTransport original substituted witness) := by
  intro forward
  intro backward
  intro witness_of_original
  exact ay_equisat_intro
    original
    (AyVisibleSccTransport original substituted witness)
    (fun horiginal =>
      ay_visible_transport_reconstruct
        original substituted witness
        horiginal
        (forward horiginal)
        (witness_of_original horiginal))
    (fun visible =>
      ay_visible_transport_project_original
        original substituted witness visible)

theorem ay_scc_context_visible_transport
    (atom : Prop) (atomSubst : Prop)
    (tailA : Prop) (tailB : Prop) :
    AyEquiv atom atomSubst ->
    AyEquisat
      (AyTwoBinaryContext atom tailA tailB)
      (AyVisibleSccTransport
        (AyTwoBinaryContext atom tailA tailB)
        (AyTwoBinaryContext atomSubst tailA tailB)
        (AyEquiv atom atomSubst)) := by
  intro atom_equiv
  exact ay_scc_visible_model_transport
    (AyTwoBinaryContext atom tailA tailB)
    (AyTwoBinaryContext atomSubst tailA tailB)
    (AyEquiv atom atomSubst)
    (ay_two_binary_context_substitute
      atom atomSubst tailA tailB atom_equiv)
    (ay_two_binary_context_reconstruct
      atom atomSubst tailA tailB atom_equiv)
    (fun _context => atom_equiv)
