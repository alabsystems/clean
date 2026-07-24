-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction for composing Tseitin gate extension, XOR/Gauss parity
-- reasoning, and commander cardinality side constraints. The package is
-- self-contained and uses Church-encoded conjunction, disjunction, and equisat.

def AyTXCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyTXCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyTXCEquisat (before : Prop) (after : Prop) :=
  AyTXCConj (before -> after) (after -> before)

def AyTXCEquiv (p : Prop) (q : Prop) :=
  AyTXCConj (p -> q) (q -> p)

def AyTXCGateFormula (gate : Prop) (context : Prop) :=
  AyTXCConj gate context

def AyTXCXorSystem (auxGate : Prop) (parityContext : Prop) :=
  AyTXCConj auxGate parityContext

def AyTXCGaussReduced (reducedGate : Prop) (parityContext : Prop) :=
  AyTXCConj reducedGate parityContext

def AyTXCCommanderAux2Cnf
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :=
  AyTXCConj
    (AyTXCDisj (Not auxA) (Not auxB))
    (AyTXCConj
      (AyTXCDisj (Not auxA) cmd)
      (AyTXCDisj (Not auxB) cmd))

def AyTXCCommanderReduced
    (reducedGate : Prop) (parityContext : Prop)
    (otherAux : Prop) (cmd : Prop) :=
  AyTXCConj
    (AyTXCGaussReduced reducedGate parityContext)
    (AyTXCCommanderAux2Cnf reducedGate otherAux cmd)

def AyTXCXorReconstruction
    (auxGate : Prop) (reducedGate : Prop) (parityContext : Prop) :=
  reducedGate -> parityContext -> auxGate

def AyTXCCommanderSideCondition
    (reducedGate : Prop) (parityContext : Prop)
    (otherAux : Prop) (cmd : Prop) :=
  AyTXCGaussReduced reducedGate parityContext ->
  AyTXCCommanderAux2Cnf reducedGate otherAux cmd

theorem ay_txc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyTXCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_txc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyTXCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_txc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyTXCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_txc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyTXCEquisat before after := by
  intro forward
  intro backward
  exact ay_txc_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_txc_equisat_forward
    (before : Prop) (after : Prop) :
    AyTXCEquisat before after ->
    before ->
    after := by
  intro cert
  exact cert (before -> after)
    (fun forward _backward => forward)

theorem ay_txc_equisat_backward
    (before : Prop) (after : Prop) :
    AyTXCEquisat before after ->
    after ->
    before := by
  intro cert
  exact cert (after -> before)
    (fun _forward backward => backward)

theorem ay_txc_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyTXCEquisat before middle ->
    AyTXCEquisat middle after ->
    AyTXCEquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_txc_equiv_forward
    (p : Prop) (q : Prop) :
    AyTXCEquiv p q ->
    p ->
    q := by
  intro equiv
  exact equiv (p -> q) (fun forward _backward => forward)

theorem ay_txc_equiv_backward
    (p : Prop) (q : Prop) :
    AyTXCEquiv p q ->
    q ->
    p := by
  intro equiv
  exact equiv (q -> p) (fun _forward backward => backward)

theorem ay_txc_pair_clause_forbids_both
    (p : Prop) (q : Prop) :
    AyTXCDisj (Not p) (Not q) -> p -> q -> False := by
  intro pair_clause
  intro hp
  intro hq
  exact pair_clause False
    (fun not_p => not_p hp)
    (fun not_q => not_q hq)

theorem ay_txc_guard_clause_implies_commander
    (lit : Prop) (cmd : Prop) :
    AyTXCDisj (Not lit) cmd -> lit -> cmd := by
  intro guard
  intro hlit
  exact guard cmd
    (fun not_lit => False.elim (not_lit hlit))
    (fun hcmd => hcmd)

theorem ay_txc_commander_forbids_both
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyTXCCommanderAux2Cnf auxA auxB cmd ->
    auxA -> auxB -> False := by
  intro commander
  intro hauxA
  intro hauxB
  exact commander False
    (fun pair_clause _guards =>
      ay_txc_pair_clause_forbids_both auxA auxB pair_clause hauxA hauxB)

theorem ay_txc_commander_auxA_implies_cmd
    (auxA : Prop) (auxB : Prop) (cmd : Prop) :
    AyTXCCommanderAux2Cnf auxA auxB cmd ->
    auxA -> cmd := by
  intro commander
  intro hauxA
  exact commander cmd
    (fun _pair_clause guards =>
      guards cmd
        (fun auxA_guard _auxB_guard =>
          ay_txc_guard_clause_implies_commander auxA cmd auxA_guard hauxA))

theorem ay_txc_tseitin_extend_gate
    (gate : Prop) (auxGate : Prop) (context : Prop) :
    AyTXCEquiv auxGate gate ->
    AyTXCGateFormula gate context ->
    AyTXCXorSystem auxGate context := by
  intro aux_equiv_gate
  intro source
  intro result
  intro build
  exact source result
    (fun hgate hcontext =>
      build
        (ay_txc_equiv_backward auxGate gate aux_equiv_gate hgate)
        hcontext)

theorem ay_txc_tseitin_project_gate
    (gate : Prop) (auxGate : Prop) (context : Prop) :
    AyTXCEquiv auxGate gate ->
    AyTXCXorSystem auxGate context ->
    AyTXCGateFormula gate context := by
  intro aux_equiv_gate
  intro source
  intro result
  intro build
  exact source result
    (fun haux hcontext =>
      build
        (ay_txc_equiv_forward auxGate gate aux_equiv_gate haux)
        hcontext)

theorem ay_txc_tseitin_equisat
    (gate : Prop) (auxGate : Prop) (context : Prop) :
    AyTXCEquiv auxGate gate ->
    AyTXCEquisat
      (AyTXCGateFormula gate context)
      (AyTXCXorSystem auxGate context) := by
  intro aux_equiv_gate
  exact ay_txc_equisat_intro
    (AyTXCGateFormula gate context)
    (AyTXCXorSystem auxGate context)
    (ay_txc_tseitin_extend_gate gate auxGate context aux_equiv_gate)
    (ay_txc_tseitin_project_gate gate auxGate context aux_equiv_gate)

theorem ay_txc_xor_gauss_project
    (auxGate : Prop) (reducedGate : Prop) (context : Prop) :
    (auxGate -> context -> reducedGate) ->
    AyTXCXorSystem auxGate context ->
    AyTXCGaussReduced reducedGate context := by
  intro reduce
  intro system
  intro result
  intro build
  exact system result
    (fun haux hcontext =>
      build (reduce haux hcontext) hcontext)

theorem ay_txc_xor_gauss_reconstruct
    (auxGate : Prop) (reducedGate : Prop) (context : Prop) :
    AyTXCXorReconstruction auxGate reducedGate context ->
    AyTXCGaussReduced reducedGate context ->
    AyTXCXorSystem auxGate context := by
  intro reconstruct
  intro reduced
  intro result
  intro build
  exact reduced result
    (fun hreduced hcontext =>
      build (reconstruct hreduced hcontext) hcontext)

theorem ay_txc_xor_gauss_equisat
    (auxGate : Prop) (reducedGate : Prop) (context : Prop) :
    (auxGate -> context -> reducedGate) ->
    AyTXCXorReconstruction auxGate reducedGate context ->
    AyTXCEquisat
      (AyTXCXorSystem auxGate context)
      (AyTXCGaussReduced reducedGate context) := by
  intro reduce
  intro reconstruct
  exact ay_txc_equisat_intro
    (AyTXCXorSystem auxGate context)
    (AyTXCGaussReduced reducedGate context)
    (ay_txc_xor_gauss_project auxGate reducedGate context reduce)
    (ay_txc_xor_gauss_reconstruct
      auxGate reducedGate context reconstruct)

theorem ay_txc_commander_extend
    (reducedGate : Prop) (context : Prop)
    (otherAux : Prop) (cmd : Prop) :
    AyTXCCommanderSideCondition reducedGate context otherAux cmd ->
    AyTXCGaussReduced reducedGate context ->
    AyTXCCommanderReduced reducedGate context otherAux cmd := by
  intro side
  intro reduced
  exact ay_txc_conj_intro
    (AyTXCGaussReduced reducedGate context)
    (AyTXCCommanderAux2Cnf reducedGate otherAux cmd)
    reduced
    (side reduced)

theorem ay_txc_commander_project
    (reducedGate : Prop) (context : Prop)
    (otherAux : Prop) (cmd : Prop) :
    AyTXCCommanderReduced reducedGate context otherAux cmd ->
    AyTXCGaussReduced reducedGate context := by
  intro with_commander
  exact with_commander
    (AyTXCGaussReduced reducedGate context)
    (fun reduced _commander => reduced)

theorem ay_txc_commander_equisat
    (reducedGate : Prop) (context : Prop)
    (otherAux : Prop) (cmd : Prop) :
    AyTXCCommanderSideCondition reducedGate context otherAux cmd ->
    AyTXCEquisat
      (AyTXCGaussReduced reducedGate context)
      (AyTXCCommanderReduced reducedGate context otherAux cmd) := by
  intro side
  exact ay_txc_equisat_intro
    (AyTXCGaussReduced reducedGate context)
    (AyTXCCommanderReduced reducedGate context otherAux cmd)
    (ay_txc_commander_extend reducedGate context otherAux cmd side)
    (ay_txc_commander_project reducedGate context otherAux cmd)

theorem ay_txc_tseitin_xor_forward
    (gate : Prop) (auxGate : Prop) (reducedGate : Prop)
    (context : Prop) :
    AyTXCEquiv auxGate gate ->
    (auxGate -> context -> reducedGate) ->
    AyTXCGateFormula gate context ->
    AyTXCGaussReduced reducedGate context := by
  intro aux_equiv_gate
  intro reduce
  intro source
  exact ay_txc_xor_gauss_project auxGate reducedGate context reduce
    (ay_txc_tseitin_extend_gate gate auxGate context
      aux_equiv_gate source)

theorem ay_txc_tseitin_xor_backward
    (gate : Prop) (auxGate : Prop) (reducedGate : Prop)
    (context : Prop) :
    AyTXCEquiv auxGate gate ->
    AyTXCXorReconstruction auxGate reducedGate context ->
    AyTXCGaussReduced reducedGate context ->
    AyTXCGateFormula gate context := by
  intro aux_equiv_gate
  intro reconstruct
  intro reduced
  exact ay_txc_tseitin_project_gate gate auxGate context aux_equiv_gate
    (ay_txc_xor_gauss_reconstruct
      auxGate reducedGate context reconstruct reduced)

theorem ay_txc_tseitin_xor_commander_forward
    (gate : Prop) (auxGate : Prop) (reducedGate : Prop)
    (context : Prop) (otherAux : Prop) (cmd : Prop) :
    AyTXCEquiv auxGate gate ->
    (auxGate -> context -> reducedGate) ->
    AyTXCCommanderSideCondition reducedGate context otherAux cmd ->
    AyTXCGateFormula gate context ->
    AyTXCCommanderReduced reducedGate context otherAux cmd := by
  intro aux_equiv_gate
  intro reduce
  intro side
  intro source
  exact ay_txc_commander_extend reducedGate context otherAux cmd side
    (ay_txc_tseitin_xor_forward
      gate auxGate reducedGate context aux_equiv_gate reduce source)

theorem ay_txc_tseitin_xor_commander_backward
    (gate : Prop) (auxGate : Prop) (reducedGate : Prop)
    (context : Prop) (otherAux : Prop) (cmd : Prop) :
    AyTXCEquiv auxGate gate ->
    AyTXCXorReconstruction auxGate reducedGate context ->
    AyTXCCommanderReduced reducedGate context otherAux cmd ->
    AyTXCGateFormula gate context := by
  intro aux_equiv_gate
  intro reconstruct
  intro transformed
  exact ay_txc_tseitin_xor_backward
    gate
    auxGate
    reducedGate
    context
    aux_equiv_gate
    reconstruct
    (ay_txc_commander_project reducedGate context otherAux cmd transformed)

theorem ay_txc_tseitin_xor_commander_equisat
    (gate : Prop) (auxGate : Prop) (reducedGate : Prop)
    (context : Prop) (otherAux : Prop) (cmd : Prop) :
    AyTXCEquiv auxGate gate ->
    (auxGate -> context -> reducedGate) ->
    AyTXCXorReconstruction auxGate reducedGate context ->
    AyTXCCommanderSideCondition reducedGate context otherAux cmd ->
    AyTXCEquisat
      (AyTXCGateFormula gate context)
      (AyTXCCommanderReduced reducedGate context otherAux cmd) := by
  intro aux_equiv_gate
  intro reduce
  intro reconstruct
  intro side
  exact ay_txc_equisat_intro
    (AyTXCGateFormula gate context)
    (AyTXCCommanderReduced reducedGate context otherAux cmd)
    (ay_txc_tseitin_xor_commander_forward
      gate auxGate reducedGate context otherAux cmd
      aux_equiv_gate reduce side)
    (ay_txc_tseitin_xor_commander_backward
      gate auxGate reducedGate context otherAux cmd
      aux_equiv_gate reconstruct)
