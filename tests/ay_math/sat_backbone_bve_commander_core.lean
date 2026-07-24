-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained backbone/BVE/commander composition kernels.
-- Propositions stand for satisfiable fragments; Church encodings keep the
-- package independent of imports.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

def AyFormulaWithUnit (formula : Prop) (unitLit : Prop) :=
  AyConj formula unitLit

def AyBackboneLiteral (formula : Prop) (unitLit : Prop) :=
  formula -> unitLit

def AyAuxWithVisible (visible : Prop) (aux : Prop) :=
  AyConj visible aux

def AyAuxReconstruction (visible : Prop) (aux : Prop) :=
  visible -> aux

def AyCommanderGroup2Cnf (x : Prop) (y : Prop) (aux : Prop) :=
  AyConj
    (AyDisj (Not x) (Not y))
    (AyConj
      (AyDisj (Not x) aux)
      (AyDisj (Not y) aux))

def AyCommanderBveChain2x2Cnf
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :=
  AyConj
    (AyCommanderGroup2Cnf a b auxAB)
    (AyConj
      (AyCommanderGroup2Cnf c d auxCD)
      (AyDisj (Not auxAB) (Not auxCD)))

def AyVisibleAmoSkeleton4 (a : Prop) (b : Prop) (c : Prop) (d : Prop) :=
  AyConj
    (a -> b -> False)
    (AyConj
      (a -> c -> False)
      (AyConj
        (a -> d -> False)
        (AyConj
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False)))))

def AyBackboneBveCommanderEncoded
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :=
  AyConj
    (AyFormulaWithUnit formula unitLit)
    (AyConj
      (AyAuxWithVisible visible aux)
      (AyCommanderBveChain2x2Cnf a b c d auxAB auxCD))

def AyBackboneBveCommanderVisible
    (formula : Prop) (unitLit : Prop) (visible : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop) :=
  AyConj
    (AyFormulaWithUnit formula unitLit)
    (AyConj visible (AyVisibleAmoSkeleton4 a b c d))

def AyCommanderReconstruction
    (visible : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :=
  visible -> AyCommanderBveChain2x2Cnf a b c d auxAB auxCD

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

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
  exact equisat (original -> transformed)
    (fun forward _backward => forward)

theorem ay_equisat_backward
    (original : Prop) (transformed : Prop) :
    AyEquisat original transformed ->
    transformed -> original := by
  intro equisat
  exact equisat (transformed -> original)
    (fun _forward backward => backward)

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

theorem ay_formula_with_unit_project_formula
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    formula := by
  intro with_unit
  exact with_unit formula
    (fun hformula _hunit => hformula)

theorem ay_formula_with_unit_project_unit
    (formula : Prop) (unitLit : Prop) :
    AyFormulaWithUnit formula unitLit ->
    unitLit := by
  intro with_unit
  exact with_unit unitLit
    (fun _hformula hunit => hunit)

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
  exact ay_formula_with_unit_project_formula formula unitLit with_unit

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

theorem ay_aux_with_visible_project_visible
    (visible : Prop) (aux : Prop) :
    AyAuxWithVisible visible aux ->
    visible := by
  intro encoded
  exact encoded visible
    (fun hvisible _haux => hvisible)

theorem ay_aux_with_visible_project_aux
    (visible : Prop) (aux : Prop) :
    AyAuxWithVisible visible aux ->
    aux := by
  intro encoded
  exact encoded aux
    (fun _hvisible haux => haux)

theorem ay_aux_elimination_reconstruct
    (visible : Prop) (aux : Prop) :
    AyAuxReconstruction visible aux ->
    visible ->
    AyAuxWithVisible visible aux := by
  intro reconstruct
  intro hvisible
  exact ay_conj_intro visible aux
    hvisible
    (reconstruct hvisible)

theorem ay_aux_elimination_equisat
    (visible : Prop) (aux : Prop) :
    AyAuxReconstruction visible aux ->
    AyEquisat (AyAuxWithVisible visible aux) visible := by
  intro reconstruct
  exact ay_equisat_intro
    (AyAuxWithVisible visible aux)
    visible
    (ay_aux_with_visible_project_visible visible aux)
    (ay_aux_elimination_reconstruct visible aux reconstruct)

theorem ay_pair_clause_forbids_both
    (p : Prop) (q : Prop) :
    AyDisj (Not p) (Not q) -> p -> q -> False := by
  intro pair_clause
  intro hp
  intro hq
  exact pair_clause False
    (fun not_p => not_p hp)
    (fun not_q => not_q hq)

theorem ay_guard_clause_reconstructs_aux
    (lit : Prop) (aux : Prop) :
    AyDisj (Not lit) aux -> lit -> aux := by
  intro guard
  intro hlit
  exact guard aux
    (fun not_lit => False.elim (not_lit hlit))
    (fun haux => haux)

theorem ay_aux_bve_projected_pair_forbids
    (left : Prop) (right : Prop)
    (leftAux : Prop) (rightAux : Prop) :
    AyDisj (Not left) leftAux ->
    AyDisj (Not right) rightAux ->
    AyDisj (Not leftAux) (Not rightAux) ->
    left -> right -> False := by
  intro left_guard
  intro right_guard
  intro aux_amo
  intro hleft
  intro hright
  exact aux_amo False
    (fun not_left_aux =>
      not_left_aux
        (ay_guard_clause_reconstructs_aux
          left leftAux left_guard hleft))
    (fun not_right_aux =>
      not_right_aux
        (ay_guard_clause_reconstructs_aux
          right rightAux right_guard hright))

theorem ay_commander_bve_chain_project_ab
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    a -> b -> False := by
  intro chain
  intro ha
  intro hb
  exact chain False
    (fun groupAB _tail =>
      groupAB False
        (fun ab_clause _guards =>
          ay_pair_clause_forbids_both a b ab_clause ha hb))

theorem ay_commander_bve_chain_project_cd
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    c -> d -> False := by
  intro chain
  intro hc
  intro hd
  exact chain False
    (fun _groupAB tail =>
      tail False
        (fun groupCD _aux_amo =>
          groupCD False
            (fun cd_clause _guards =>
              ay_pair_clause_forbids_both c d cd_clause hc hd)))

theorem ay_commander_bve_chain_project_ac
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    a -> c -> False := by
  intro chain
  intro ha
  intro hc
  exact chain False
    (fun groupAB tail =>
      tail False
        (fun groupCD aux_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun a_to_aux _b_to_aux =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun c_to_aux _d_to_aux =>
                          ay_aux_bve_projected_pair_forbids
                            a c auxAB auxCD
                            a_to_aux c_to_aux aux_amo ha hc)))))))

theorem ay_commander_bve_chain_project_ad
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    a -> d -> False := by
  intro chain
  intro ha
  intro hd
  exact chain False
    (fun groupAB tail =>
      tail False
        (fun groupCD aux_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun a_to_aux _b_to_aux =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun _c_to_aux d_to_aux =>
                          ay_aux_bve_projected_pair_forbids
                            a d auxAB auxCD
                            a_to_aux d_to_aux aux_amo ha hd)))))))

theorem ay_commander_bve_chain_project_bc
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    b -> c -> False := by
  intro chain
  intro hb
  intro hc
  exact chain False
    (fun groupAB tail =>
      tail False
        (fun groupCD aux_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun _a_to_aux b_to_aux =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun c_to_aux _d_to_aux =>
                          ay_aux_bve_projected_pair_forbids
                            b c auxAB auxCD
                            b_to_aux c_to_aux aux_amo hb hc)))))))

theorem ay_commander_bve_chain_project_bd
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    b -> d -> False := by
  intro chain
  intro hb
  intro hd
  exact chain False
    (fun groupAB tail =>
      tail False
        (fun groupCD aux_amo =>
          groupAB False
            (fun _ab_clause ab_guards =>
              ab_guards False
                (fun _a_to_aux b_to_aux =>
                  groupCD False
                    (fun _cd_clause cd_guards =>
                      cd_guards False
                        (fun _c_to_aux d_to_aux =>
                          ay_aux_bve_projected_pair_forbids
                            b d auxAB auxCD
                            b_to_aux d_to_aux aux_amo hb hd)))))))

theorem ay_visible_amo_skeleton4_intro
    (a : Prop) (b : Prop) (c : Prop) (d : Prop) :
    (a -> b -> False) ->
    (a -> c -> False) ->
    (a -> d -> False) ->
    (b -> c -> False) ->
    (b -> d -> False) ->
    (c -> d -> False) ->
    AyVisibleAmoSkeleton4 a b c d := by
  intro ab
  intro ac
  intro ad
  intro bc
  intro bd
  intro cd
  intro result
  intro build
  exact build ab
    (ay_conj_intro
      (a -> c -> False)
      (AyConj
        (a -> d -> False)
        (AyConj
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False))))
      ac
      (ay_conj_intro
        (a -> d -> False)
        (AyConj
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False)))
        ad
        (ay_conj_intro
          (b -> c -> False)
          (AyConj
            (b -> d -> False)
            (c -> d -> False))
          bc
          (ay_conj_intro
            (b -> d -> False)
            (c -> d -> False)
            bd
            cd))))

theorem ay_commander_bve_chain_preserves_visible_amo
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD ->
    AyVisibleAmoSkeleton4 a b c d := by
  intro chain
  exact ay_visible_amo_skeleton4_intro a b c d
    (ay_commander_bve_chain_project_ab
      a b c d auxAB auxCD chain)
    (ay_commander_bve_chain_project_ac
      a b c d auxAB auxCD chain)
    (ay_commander_bve_chain_project_ad
      a b c d auxAB auxCD chain)
    (ay_commander_bve_chain_project_bc
      a b c d auxAB auxCD chain)
    (ay_commander_bve_chain_project_bd
      a b c d auxAB auxCD chain)
    (ay_commander_bve_chain_project_cd
      a b c d auxAB auxCD chain)

theorem ay_encoded_project_unit
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD ->
    AyFormulaWithUnit formula unitLit := by
  intro encoded
  exact encoded (AyFormulaWithUnit formula unitLit)
    (fun with_unit _tail => with_unit)

theorem ay_encoded_project_visible_aux
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD ->
    AyAuxWithVisible visible aux := by
  intro encoded
  exact encoded (AyAuxWithVisible visible aux)
    (fun _with_unit tail =>
      tail (AyAuxWithVisible visible aux)
        (fun visible_aux _commander => visible_aux))

theorem ay_encoded_project_commander
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD ->
    AyCommanderBveChain2x2Cnf a b c d auxAB auxCD := by
  intro encoded
  exact encoded (AyCommanderBveChain2x2Cnf a b c d auxAB auxCD)
    (fun _with_unit tail =>
      tail (AyCommanderBveChain2x2Cnf a b c d auxAB auxCD)
        (fun _visible_aux commander => commander))

theorem ay_encoded_to_visible_forward
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD ->
    AyBackboneBveCommanderVisible formula unitLit visible a b c d := by
  intro encoded
  exact ay_conj_intro
    (AyFormulaWithUnit formula unitLit)
    (AyConj visible (AyVisibleAmoSkeleton4 a b c d))
    (ay_encoded_project_unit
      formula unitLit visible aux a b c d auxAB auxCD encoded)
    (ay_conj_intro visible (AyVisibleAmoSkeleton4 a b c d)
      (ay_aux_with_visible_project_visible visible aux
        (ay_encoded_project_visible_aux
          formula unitLit visible aux a b c d auxAB auxCD encoded))
      (ay_commander_bve_chain_preserves_visible_amo
        a b c d auxAB auxCD
        (ay_encoded_project_commander
          formula unitLit visible aux a b c d auxAB auxCD encoded)))

theorem ay_visible_to_encoded_backward
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyAuxReconstruction visible aux ->
    AyCommanderReconstruction visible a b c d auxAB auxCD ->
    AyBackboneBveCommanderVisible formula unitLit visible a b c d ->
    AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD := by
  intro aux_reconstruct
  intro commander_reconstruct
  intro visible_formula
  exact visible_formula
    (AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD)
    (fun with_unit tail =>
      tail
        (AyBackboneBveCommanderEncoded
          formula unitLit visible aux a b c d auxAB auxCD)
        (fun hvisible _amo =>
          ay_conj_intro
            (AyFormulaWithUnit formula unitLit)
            (AyConj
              (AyAuxWithVisible visible aux)
              (AyCommanderBveChain2x2Cnf a b c d auxAB auxCD))
            with_unit
            (ay_conj_intro
              (AyAuxWithVisible visible aux)
              (AyCommanderBveChain2x2Cnf a b c d auxAB auxCD)
              (ay_aux_elimination_reconstruct
                visible aux aux_reconstruct hvisible)
              (commander_reconstruct hvisible))))

theorem ay_visible_formula_equisat_transport
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyAuxReconstruction visible aux ->
    AyCommanderReconstruction visible a b c d auxAB auxCD ->
    AyEquisat
      (AyBackboneBveCommanderEncoded
        formula unitLit visible aux a b c d auxAB auxCD)
      (AyBackboneBveCommanderVisible
        formula unitLit visible a b c d) := by
  intro aux_reconstruct
  intro commander_reconstruct
  exact ay_equisat_intro
    (AyBackboneBveCommanderEncoded
      formula unitLit visible aux a b c d auxAB auxCD)
    (AyBackboneBveCommanderVisible
      formula unitLit visible a b c d)
    (ay_encoded_to_visible_forward
      formula unitLit visible aux a b c d auxAB auxCD)
    (ay_visible_to_encoded_backward
      formula unitLit visible aux a b c d auxAB auxCD
      aux_reconstruct commander_reconstruct)

theorem ay_backbone_unit_then_visible_transport
    (formula : Prop) (unitLit : Prop) (visible : Prop) (aux : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (auxAB : Prop) (auxCD : Prop) :
    AyBackboneLiteral formula unitLit ->
    AyAuxReconstruction visible aux ->
    AyCommanderReconstruction visible a b c d auxAB auxCD ->
    AyEquisat
      (AyFormulaWithUnit formula unitLit)
      (AyBackboneBveCommanderEncoded
        formula unitLit visible aux a b c d auxAB auxCD) ->
    AyEquisat
      formula
      (AyBackboneBveCommanderVisible
        formula unitLit visible a b c d) := by
  intro backbone
  intro aux_reconstruct
  intro commander_reconstruct
  intro unit_to_encoded
  exact ay_equisat_trans
    formula
    (AyFormulaWithUnit formula unitLit)
    (AyBackboneBveCommanderVisible
      formula unitLit visible a b c d)
    (ay_backbone_unit_add_equisat formula unitLit backbone)
    (ay_equisat_trans
      (AyFormulaWithUnit formula unitLit)
      (AyBackboneBveCommanderEncoded
        formula unitLit visible aux a b c d auxAB auxCD)
      (AyBackboneBveCommanderVisible
        formula unitLit visible a b c d)
      unit_to_encoded
      (ay_visible_formula_equisat_transport
        formula unitLit visible aux a b c d auxAB auxCD
        aux_reconstruct commander_reconstruct))
