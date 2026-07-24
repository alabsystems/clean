-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-contained cardinality/commander BVE-chain kernels.
-- Commander auxiliaries are projected away by resolving visible-to-commander
-- guards with commander at-most-one clauses.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (original : Prop) (transformed : Prop) :=
  AyConj (original -> transformed) (transformed -> original)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

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
