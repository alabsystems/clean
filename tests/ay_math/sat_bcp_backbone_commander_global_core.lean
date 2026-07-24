-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems composing BCP/HBR/backbone discovery with
-- BVE/commander visible-cardinality encodings. This package is self-contained
-- and uses Church-encoded conjunction, disjunction, and equisatisfiability.

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyBinaryImp (source : Prop) (target : Prop) :=
  AyDisj (Not source) target

def AyHbrParents (source : Prop) (middle : Prop) (target : Prop) :=
  AyConj (AyBinaryImp source middle) (AyBinaryImp middle target)

def AyFormulaWithUnit (formula : Prop) (unitLit : Prop) :=
  AyConj formula unitLit

def AyBackboneLiteral (formula : Prop) (unitLit : Prop) :=
  formula -> unitLit

def AyCommanderGroup2Cnf (x : Prop) (y : Prop) (cmd : Prop) :=
  AyConj
    (AyDisj (Not x) (Not y))
    (AyConj
      (AyDisj (Not x) cmd)
      (AyDisj (Not y) cmd))

def AyCommanderBveProjected2x2
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyConj
    (AyCommanderGroup2Cnf a b cmdAB)
    (AyConj
      (AyCommanderGroup2Cnf c d cmdCD)
      (AyDisj (Not cmdAB) (Not cmdCD)))

def AyProjectedAmoSkeleton4
    (a : Prop) (b : Prop) (c : Prop) (d : Prop) :=
  AyConj
    (a -> b -> False)
    (AyConj
      (c -> d -> False)
      (AyConj
        (a -> c -> False)
        (b -> d -> False)))

def AyGlobalPipelineInput
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyConj formula
    (AyConj
      (AyHbrParents unit middle target)
      (AyCommanderBveProjected2x2 a b c d cmdAB cmdCD))

def AyGlobalVisibleModel
    (original : Prop) (unitLit : Prop)
    (derivedBinary : Prop) (amo : Prop) :=
  AyConj original (AyConj unitLit (AyConj derivedBinary amo))

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

theorem ay_bcp_conflict_sound
    (unit : Prop) :
    unit ->
    AyBinaryImp unit False ->
    False := by
  intro hunit
  intro conflict_clause
  exact ay_bcp_unit_propagates_binary unit False hunit conflict_clause

theorem ay_backbone_unit_add_forward
    (formula : Prop) (unitLit : Prop) :
    AyBackboneLiteral formula unitLit ->
    formula ->
    AyFormulaWithUnit formula unitLit := by
  intro backbone
  intro hformula
  exact ay_conj_intro formula unitLit
    hformula
    (backbone hformula)

theorem ay_backbone_unit_add_backward
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
    (ay_backbone_unit_add_forward formula unitLit backbone)
    (ay_backbone_unit_add_backward formula unitLit)

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

theorem ay_pair_clause_forbids_both
    (p : Prop) (q : Prop) :
    AyDisj (Not p) (Not q) -> p -> q -> False := by
  intro pair_clause
  intro hp
  intro hq
  exact pair_clause False
    (fun not_p => not_p hp)
    (fun not_q => not_q hq)

theorem ay_guard_clause_implies_commander
    (lit : Prop) (commander : Prop) :
    AyDisj (Not lit) commander -> lit -> commander := by
  intro guard
  intro hlit
  exact guard commander
    (fun not_lit => False.elim (not_lit hlit))
    (fun hcommander => hcommander)

theorem ay_commander_aux_bve_projected_pair_forbids
    (lit : Prop) (other : Prop) (commander : Prop) :
    AyDisj (Not lit) commander ->
    AyDisj (Not commander) (Not other) ->
    lit -> other -> False := by
  intro guard
  intro commander_amo
  intro hlit
  intro hother
  exact commander_amo False
    (fun not_commander =>
      not_commander
        (ay_guard_clause_implies_commander lit commander guard hlit))
    (fun not_other => not_other hother)

theorem ay_commander_bve_preserves_local_pair_ab
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    a -> b -> False := by
  intro encoded
  intro ha
  intro hb
  exact encoded False
    (fun groupAB _tail =>
      groupAB False
        (fun ab_clause _guards =>
          ay_pair_clause_forbids_both a b ab_clause ha hb))

theorem ay_commander_bve_preserves_local_pair_cd
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    c -> d -> False := by
  intro encoded
  intro hc
  intro hd
  exact encoded False
    (fun _groupAB tail =>
      tail False
        (fun groupCD _commander_amo =>
          groupCD False
            (fun cd_clause _guards =>
              ay_pair_clause_forbids_both c d cd_clause hc hd)))

theorem ay_commander_bve_projects_a_c_pair
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    a -> c -> False := by
  intro encoded
  intro ha
  intro hc
  exact encoded False
    (fun groupAB tail =>
      tail False
        (fun groupCD commander_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun a_to_cmd _b_to_cmd =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun c_to_cmd _d_to_cmd =>
                          ay_commander_aux_bve_projected_pair_forbids
                            a cmdCD cmdAB
                            a_to_cmd commander_amo
                            ha
                            (ay_guard_clause_implies_commander
                              c cmdCD c_to_cmd hc))))))))

theorem ay_commander_bve_projects_b_d_pair
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    b -> d -> False := by
  intro encoded
  intro hb
  intro hd
  exact encoded False
    (fun groupAB tail =>
      tail False
        (fun groupCD commander_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun _a_to_cmd b_to_cmd =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun _c_to_cmd d_to_cmd =>
                          ay_commander_aux_bve_projected_pair_forbids
                            b cmdCD cmdAB
                            b_to_cmd commander_amo
                            hb
                            (ay_guard_clause_implies_commander
                              d cmdCD d_to_cmd hd))))))))

theorem ay_commander_bve_visible_amo
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD ->
    AyProjectedAmoSkeleton4 a b c d := by
  intro encoded
  intro result
  intro build
  exact build
    (ay_commander_bve_preserves_local_pair_ab
      a b c d cmdAB cmdCD encoded)
    (ay_conj_intro
      (c -> d -> False)
      (AyConj (a -> c -> False) (b -> d -> False))
      (ay_commander_bve_preserves_local_pair_cd
        a b c d cmdAB cmdCD encoded)
      (ay_conj_intro
        (a -> c -> False)
        (b -> d -> False)
        (ay_commander_bve_projects_a_c_pair
          a b c d cmdAB cmdCD encoded)
        (ay_commander_bve_projects_b_d_pair
          a b c d cmdAB cmdCD encoded)))

theorem ay_global_input_project_formula
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    formula := by
  intro input
  exact ay_conj_left formula
    (AyConj
      (AyHbrParents unit middle target)
      (AyCommanderBveProjected2x2 a b c d cmdAB cmdCD))
    input

theorem ay_global_input_project_hbr
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    AyHbrParents unit middle target := by
  intro input
  exact ay_conj_left
    (AyHbrParents unit middle target)
    (AyCommanderBveProjected2x2 a b c d cmdAB cmdCD)
    (ay_conj_right formula
      (AyConj
        (AyHbrParents unit middle target)
        (AyCommanderBveProjected2x2 a b c d cmdAB cmdCD))
      input)

theorem ay_global_input_project_commander
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    AyCommanderBveProjected2x2 a b c d cmdAB cmdCD := by
  intro input
  exact ay_conj_right
    (AyHbrParents unit middle target)
    (AyCommanderBveProjected2x2 a b c d cmdAB cmdCD)
    (ay_conj_right formula
      (AyConj
        (AyHbrParents unit middle target)
        (AyCommanderBveProjected2x2 a b c d cmdAB cmdCD))
      input)

theorem ay_global_pipeline_derive_binary
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    AyBinaryImp unit target := by
  intro input
  exact ay_hbr_parents_derive_binary unit middle target
    (ay_global_input_project_hbr
      formula unit middle target a b c d cmdAB cmdCD input)

theorem ay_global_pipeline_derive_unit
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyBackboneLiteral formula unit ->
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    AyFormulaWithUnit formula unit := by
  intro backbone
  intro input
  exact ay_backbone_unit_add_forward formula unit backbone
    (ay_global_input_project_formula
      formula unit middle target a b c d cmdAB cmdCD input)

theorem ay_global_pipeline_derive_amo
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    AyProjectedAmoSkeleton4 a b c d := by
  intro input
  exact ay_commander_bve_visible_amo a b c d cmdAB cmdCD
    (ay_global_input_project_commander
      formula unit middle target a b c d cmdAB cmdCD input)

theorem ay_global_visible_reconstruct
    (original : Prop) (unitLit : Prop)
    (derivedBinary : Prop) (amo : Prop) :
    original ->
    unitLit ->
    derivedBinary ->
    amo ->
    AyGlobalVisibleModel original unitLit derivedBinary amo := by
  intro horiginal
  intro hunit
  intro hderived
  intro hamo
  exact ay_conj_intro original
    (AyConj unitLit (AyConj derivedBinary amo))
    horiginal
    (ay_conj_intro unitLit (AyConj derivedBinary amo)
      hunit
      (ay_conj_intro derivedBinary amo hderived hamo))

theorem ay_global_visible_project_original
    (original : Prop) (unitLit : Prop)
    (derivedBinary : Prop) (amo : Prop) :
    AyGlobalVisibleModel original unitLit derivedBinary amo ->
    original := by
  intro visible
  exact ay_conj_left original
    (AyConj unitLit (AyConj derivedBinary amo))
    visible

theorem ay_global_visible_project_unit
    (original : Prop) (unitLit : Prop)
    (derivedBinary : Prop) (amo : Prop) :
    AyGlobalVisibleModel original unitLit derivedBinary amo ->
    unitLit := by
  intro visible
  exact ay_conj_left unitLit (AyConj derivedBinary amo)
    (ay_conj_right original
      (AyConj unitLit (AyConj derivedBinary amo))
      visible)

theorem ay_global_visible_project_binary
    (original : Prop) (unitLit : Prop)
    (derivedBinary : Prop) (amo : Prop) :
    AyGlobalVisibleModel original unitLit derivedBinary amo ->
    derivedBinary := by
  intro visible
  exact ay_conj_left derivedBinary amo
    (ay_conj_right unitLit (AyConj derivedBinary amo)
      (ay_conj_right original
        (AyConj unitLit (AyConj derivedBinary amo))
        visible))

theorem ay_global_visible_project_amo
    (original : Prop) (unitLit : Prop)
    (derivedBinary : Prop) (amo : Prop) :
    AyGlobalVisibleModel original unitLit derivedBinary amo ->
    amo := by
  intro visible
  exact ay_conj_right derivedBinary amo
    (ay_conj_right unitLit (AyConj derivedBinary amo)
      (ay_conj_right original
        (AyConj unitLit (AyConj derivedBinary amo))
        visible))

theorem ay_global_pipeline_forward
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyBackboneLiteral formula unit ->
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD ->
    AyGlobalVisibleModel
      (AyGlobalPipelineInput formula unit middle target
        a b c d cmdAB cmdCD)
      unit
      (AyBinaryImp unit target)
      (AyProjectedAmoSkeleton4 a b c d) := by
  intro backbone
  intro input
  exact ay_conj_intro
    (AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD)
    (AyConj unit
      (AyConj
        (AyBinaryImp unit target)
        (AyProjectedAmoSkeleton4 a b c d)))
    input
    (ay_conj_intro unit
      (AyConj
        (AyBinaryImp unit target)
        (AyProjectedAmoSkeleton4 a b c d))
      (backbone
        (ay_global_input_project_formula
          formula unit middle target a b c d cmdAB cmdCD input))
      (ay_conj_intro
        (AyBinaryImp unit target)
        (AyProjectedAmoSkeleton4 a b c d)
        (ay_global_pipeline_derive_binary
          formula unit middle target a b c d cmdAB cmdCD input)
        (ay_global_pipeline_derive_amo
          formula unit middle target a b c d cmdAB cmdCD input)))

theorem ay_global_pipeline_backward
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyGlobalVisibleModel
      (AyGlobalPipelineInput formula unit middle target
        a b c d cmdAB cmdCD)
      unit
      (AyBinaryImp unit target)
      (AyProjectedAmoSkeleton4 a b c d) ->
    AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD := by
  intro visible
  exact ay_global_visible_project_original
    (AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD)
    unit
    (AyBinaryImp unit target)
    (AyProjectedAmoSkeleton4 a b c d)
    visible

theorem ay_global_pipeline_visible_equisat
    (formula : Prop) (unit : Prop)
    (middle : Prop) (target : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyBackboneLiteral formula unit ->
    AyEquisat
      (AyGlobalPipelineInput formula unit middle target
        a b c d cmdAB cmdCD)
      (AyGlobalVisibleModel
        (AyGlobalPipelineInput formula unit middle target
          a b c d cmdAB cmdCD)
        unit
        (AyBinaryImp unit target)
        (AyProjectedAmoSkeleton4 a b c d)) := by
  intro backbone
  exact ay_equisat_intro
    (AyGlobalPipelineInput formula unit middle target
      a b c d cmdAB cmdCD)
    (AyGlobalVisibleModel
      (AyGlobalPipelineInput formula unit middle target
        a b c d cmdAB cmdCD)
      unit
      (AyBinaryImp unit target)
      (AyProjectedAmoSkeleton4 a b c d))
    (ay_global_pipeline_forward
      formula unit middle target a b c d cmdAB cmdCD backbone)
    (ay_global_pipeline_backward
      formula unit middle target a b c d cmdAB cmdCD)
